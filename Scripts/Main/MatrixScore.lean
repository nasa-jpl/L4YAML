module

public import Scripts.Matrix.Score

/-!
# `lake run matrix-score -- --data DIR …` — the YAML-processor scorer

The port of `scripts/matrix_score.py` (Rule 9 phase 4 row 2): every processor —
L4YAML's native `l4yaml-event` / `l4yaml-json` and the docker testers of the
`yamlall` container — runs over every leaf of the yaml-test-suite *data* form
through this one harness, so the numbers are apples-to-apples with
http://matrix.yaml.info.  The readings are `Scripts.Matrix.Score`; this is the IO:
the directory walk, the testers (each under `--timeout`, through `sh` with a start
mark inside docker so a reply that never reached the tester is a harness failure,
not a rejection), the `--workers` pool, the stderr table and `--out`.

A tester the harness cannot start (wrong path, no `docker`, missing container or
tester) and an unusable `in.json` oracle score `harness-error`, never
`err-ok`/`reject`/`diff`, and the run exits 1.

exit status: 0 every selected tester ran; 1 a harness failure (the scores are not
publishable); 2 usage.
-/

namespace Scripts.MatrixScore

open Scripts.Matrix.Score

def version : String := "scripts-matrix-score 1.0 (Rule 9 phase 4 row 2)"

def usage : String := "usage: lake run matrix-score -- --data DIR [options]

  -d, --data DIR          the yaml-test-suite data form (required; `tags/`, `name/` skipped)
  -c, --container NAME    the docker container holding the testers (default: yamlall)
  -a, --axis event|json|both   (default: both)
  -t, --timeout SECS      per-test deadline, killed after (default: 5.0)
  -w, --workers N         concurrent testers (default: 8)
  -e, --l4yaml-event CMD  L4YAML's event tester (absolute path; a bare name is looked up on PATH)
  -j, --l4yaml-json CMD   L4YAML's json tester
  -o, --only IDS          comma-separated processor ids (default: all)
  -O, --out FILE          write the results JSON
  -C, --root ROOT         base of relative paths (default: the current directory)
  -h, --help / -V, --version

Prints one line per processor and axis on stderr; exit 1 when the harness itself failed."

structure Opts where
  root : System.FilePath := "."
  data : Option String := none
  container : String := "yamlall"
  axis : String := "both"
  timeoutMs : Nat := 5000
  workers : Nat := 8
  l4Event : Option String := none
  l4Json : Option String := none
  only : Option (List String) := none
  out : Option String := none

/-- `--opt value` or `--opt=value`, each with its short form. -/
partial def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | arg :: rest, o =>
    let (name, inline) := match arg.splitOn "=" with
      | n :: v :: more => (n, some ("=".intercalate (v :: more)))
      | _ => (arg, none)
    let withValue (k : String → Opts → Except String Opts) : Except String Opts :=
      match inline, rest with
      | some v, _ => k v o >>= parseArgs rest
      | none, v :: rest' => k v o >>= parseArgs rest'
      | none, [] => .error s!"{name} requires a value"
    match name with
    | "-d" | "--data" => withValue fun v o => .ok { o with data := some v }
    | "-c" | "--container" => withValue fun v o => .ok { o with container := v }
    | "-a" | "--axis" => withValue fun v o =>
        if v == "event" || v == "json" || v == "both" then .ok { o with axis := v }
        else .error s!"--axis: invalid choice: '{v}' (choose from 'event', 'json', 'both')"
    | "-t" | "--timeout" => withValue fun v o =>
        match parseSeconds v with
        | some ms => .ok { o with timeoutMs := ms }
        | none => .error s!"--timeout: invalid float value: '{v}'"
    | "-w" | "--workers" => withValue fun v o =>
        match v.toNat? with
        | some n => .ok { o with workers := n }
        | none => .error s!"--workers: invalid int value: '{v}'"
    | "-e" | "--l4yaml-event" => withValue fun v o => .ok { o with l4Event := some v }
    | "-j" | "--l4yaml-json" => withValue fun v o => .ok { o with l4Json := some v }
    | "-o" | "--only" => withValue fun v o => .ok { o with only := some (v.splitOn ",") }
    | "-O" | "--out" => withValue fun v o => .ok { o with out := some v }
    | "-C" | "--root" => withValue fun v o => .ok { o with root := v }
    | _ => .error s!"unrecognized argument: {arg}"

def underRoot (root : System.FilePath) (p : String) : System.FilePath :=
  if System.FilePath.isAbsolute p then p else root / p

/-- A tester command: `#["docker", "exec", "-i", container, tester]` or the native binary. -/
abbrev Cmd := Array String

def isDocker (cmd : Cmd) : Bool := cmd[0]? == some "docker"

def startMark : ByteArray := ByteArray.mk #[0] ++ "L4YAML-TESTER-STARTED\n".toUTF8

/-- `docker exec -i C T` → the same through `sh`, which prints `startMark` before
    exec'ing the tester: a reply without the mark never reached the tester. -/
def dockerWrapped (cmd : Cmd) : Cmd :=
  #["docker", "exec", "-i", cmd[3]!, "sh", "-c",
    "printf \"\\000L4YAML-TESTER-STARTED\\n\"; exec \"$1\"", "sh", cmd[4]!] ++ cmd.extract 5 cmd.size

def lossy (b : ByteArray) : String := (String.fromUTF8? b).getD ""

/-- Feed `input` to the tester's stdin and close it; a tester that exited or stopped
    reading (EPIPE) is not the feeder's concern. -/
def feed (stdin : IO.FS.Handle) (input : ByteArray) : IO Unit := do
  try stdin.write input; stdin.flush catch _ => pure ()

/-- Run `argv` with `input` on stdin, both outputs captured, killed after `limitMs`
    (`none`).  The clock starts before the feeder and the readers, each on its own
    task, so a tester that neither reads nor exits is killed at the deadline — its
    whole process group, which closes the pipes under the blocked feeder and
    readers.  Spawn failures propagate. -/
def outputWithin (limitMs : Nat) (argv : Cmd) (input : ByteArray) :
    IO (Option (UInt32 × ByteArray × ByteArray)) := do
  let child ← IO.Process.spawn
    { cmd := argv[0]!, args := argv.extract 1 argv.size,
      stdin := .piped, stdout := .piped, stderr := .piped, setsid := true }
  let (stdin, child) ← child.takeStdin
  let start ← IO.monoMsNow
  discard <| IO.asTask (prio := .dedicated) (feed stdin input)
  let outT ← IO.asTask (prio := .dedicated) child.stdout.readBinToEnd
  let errT ← IO.asTask (prio := .dedicated) child.stderr.readBinToEnd
  let mut rc : UInt32 := 0
  repeat
    if let some code ← child.tryWait then rc := code; break   -- tryWait reaps: no wait after it
    if (← IO.monoMsNow) - start > limitMs then
      -- the tester's whole process group (`setsid`): what `sh` exec'd or left behind
      -- would otherwise hold the pipes open and the reader tasks with them
      unless System.Platform.isWindows do
        discard <| IO.Process.output { cmd := "kill", args := #["-9", "--", s!"-{child.pid}"] }
      child.kill
      discard child.wait
      return none
    IO.sleep 10
  return some (rc, ← IO.ofExcept outT.get, ← IO.ofExcept errT.get)

/-- The harness failures reported so far (first-seen order; each printed once). -/
abbrev Reported := IO.Ref (List String)

def harnessError (rep : Reported) (msg : String) : IO String := do
  -- one atomic step: workers report concurrently, and the final count is this list's length
  let isNew ← rep.modifyGet fun seen =>
    if seen.contains msg then (false, seen) else (true, seen ++ [msg])
  if isNew then IO.eprintln s!"# harness error: {msg}"
  pure "harness-error"

/-- Python `run`: `(rc, stdout)`; `unstarted` when the tester could not be started at
    all, `timeout` when the harness killed it. -/
def run (rep : Reported) (cmd : Cmd) (input : ByteArray) (limitMs : Nat) : IO (Rc × ByteArray) := do
  let dockered := isDocker cmd
  let r ← try outputWithin limitMs (if dockered then dockerWrapped cmd else cmd) input
    catch e => do
      discard <| harnessError rep s!"cannot run {cmd[0]!}: {e}"
      return (.unstarted, .empty)
  match r with
  | none => return (.timeout, .empty)
  | some (rc, out, err) =>
    if dockered then
      if out.size ≥ startMark.size && out.extract 0 startMark.size == startMark then
        return (.code rc, out.extract startMark.size out.size)
      let lines := ((lossy err).trimAscii.toString.splitOn "\n").filter (· != "")
      discard <| harnessError rep s!"docker exec did not reach {cmd[4]!} in {cmd[3]!}: {lines.getLast?.getD s!"rc={rc}"}"
      return (.unstarted, .empty)
    return (.code rc, out)

/-- `shutil.which`: a command with a separator is a file; a bare name is searched on PATH. -/
def onPath (cmd : String) : IO Bool := do
  let isFile (p : System.FilePath) : IO Bool := do
    match ← p.metadata.toBaseIO with
    | .ok m => pure (m.type == .file)
    | .error _ => pure false
  if cmd.any (fun c => c == '/' || c == '\\') then isFile cmd
  else
    let sep := if System.Platform.isWindows then ";" else ":"
    let dirs := ((← IO.getEnv "PATH").getD "").splitOn sep
    dirs.anyM fun d => if d.isEmpty then pure false else isFile (System.FilePath.mk d / cmd)

/-- Python `tester_available`: `none` if the tester can be started, else why not.
    `docker exec` exits nonzero on its own when the container is missing or stopped
    or the tester is not in the image; scored blind those would pass for rejections. -/
def testerAvailable (cmd : Cmd) : IO (Option String) := do
  if !isDocker cmd then
    return if ← onPath cmd[0]! then none else some s!"{cmd[0]!} is not an executable file (or not on PATH)"
  let (container, tester) := (cmd[3]!, cmd[4]!)
  let probe := #["docker", "exec", container, "sh", "-c", "command -v \"$1\"", "sh", tester]
  let r ← try outputWithin 60000 probe .empty catch e => return some s!"cannot run docker: {e}"
  match r with
  | none => return some "cannot run docker: the 60 s probe timed out"
  | some (rc, _, err) =>
    if rc == 0 then return none
    let e := (lossy err).trimAscii.toString
    return some s!"{tester} not runnable in container {container}: {if e.isEmpty then s!"rc={rc}" else e}"

def noOracle (d : System.FilePath) (axis : String) : IO Bool := do
  pure (axis == "json" && !(← (d / "in.json").pathExists))

/-- Python `score_one`: `(category, testid)`. -/
def scoreOne (rep : Reported) (cmd : Cmd) (d : System.FilePath) (axis : String) (limitMs : Nat) :
    IO (String × String) := do
  let tid := testId d.toString
  if ← noOracle d axis then return ("skip", tid)
  let inp ← IO.FS.readBinFile (d / "in.yaml")
  let isErr ← (d / "error").pathExists
  if axis == "event" then
    let (rc, out) ← run rep cmd inp limitMs
    if let some cat := rcCategory rc isErr then return (cat, tid)
    let exp ← IO.FS.readFile (d / "test.event")
    match String.fromUTF8? out with
    | some got => return (eventVerdict got exp, tid)
    | none => return ("diff", tid)
  else
    -- the oracle is read before the tester's verdict can short-circuit: a bad in.json
    -- is the harness's fault whether or not the tester rejected the input; error tests
    -- are exempt (9MQT/01, DK95/01, DK95/06 carry a stale in.json)
    let mut exp : List Lean.Json := []
    if !isErr then
      let text ← try pure (.ok (← IO.FS.readFile (d / "in.json"))) catch e => pure (.error s!"{e}")
      match text >>= parseJsonStream with
      | .ok v => exp := v
      | .error e => return (← harnessError rep s!"unusable oracle {d / "in.json"}: {e}", tid)
    let (rc, out) ← run rep cmd inp limitMs
    if let some cat := rcCategory rc isErr then return (cat, tid)
    match String.fromUTF8? out with
    | some got => return (jsonVerdict got exp, tid)
    | none => return ("diff", tid)

/-- `ThreadPoolExecutor(max_workers=workers).map`: `workers` dedicated threads take the
    next index; results in input order. -/
def pmap {α β : Type} (workers : Nat) (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate xs.size (none : Option (Except IO.Error β)))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then
        let r ← try pure (.ok (← f xs[i])) catch e => pure (.error e)
        results.modify (·.set! i (some r))
      else break
  let tasks ← (List.range (max 1 workers)).mapM fun _ => IO.asTask (prio := .dedicated) worker
  for t in tasks do IO.ofExcept (← IO.wait t)
  (← results.get).mapM fun
    | some (.ok b) => pure b
    | some (.error e) => throw e
    | none => throw (IO.userError "pmap: a result is missing")

/-- Python `score`: preflight once, then every leaf through the pool. -/
def score (rep : Reported) (cmd : Cmd) (dirs : Array System.FilePath) (axis : String)
    (limitMs workers : Nat) : IO AxisResult := do
  let reason ← testerAvailable cmd
  if let some r := reason then discard <| harnessError rep r
  let rs ← pmap workers dirs fun d => do
    if reason.isSome then   -- tester cannot start: skip what scoreOne would skip, fail the rest
      return (if ← noOracle d axis then "skip" else "harness-error", testId d.toString)
    scoreOne rep cmd d axis limitMs
  let mut cats : List (String × Nat) := []
  let mut fails : List (String × String) := []
  for (cat, tid) in rs do
    cats := bump cats cat
    if isFail cat then fails := fails ++ [(cat, tid)]
  return ⟨cats, fails⟩

/-- Python `leaf_dirs`: every directory holding an `in.yaml`, the `tags/` and `name/`
    symlink index dirs skipped, sorted. -/
def leafDirs (data : System.FilePath) : IO (Array System.FilePath) := do
  let index (p : System.FilePath) : Bool := p.fileName == some "tags" || p.fileName == some "name"
  let files ← data.walkDir (enter := fun p => pure (!index p))
  let dirs := files.filterMap fun p =>
    if p.fileName == some "in.yaml" && !p.components.any (fun c => c == "tags" || c == "name") then p.parent
    else none
  pure (dirs.qsort (fun a b => a.toString < b.toString))

def die (msg : String) (code : UInt32 := 2) : IO UInt32 := do
  IO.eprintln msg; pure code

def cli (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => return ← die s!"{usage}\nerror: {e}"
  let some data := o.data | return ← die s!"{usage}\nerror: the following arguments are required: --data"
  let dataDir := underRoot o.root data
  let dirs ← leafDirs dataDir
  IO.eprintln s!"# {dirs.size} leaf tests in data form"
  let native (c : String) : String :=
    if c.any (fun ch => ch == '/' || ch == '\\') then (underRoot o.root c).toString else c
  -- processor → [(axis, cmd)]
  let mut procs : List (String × List (String × Cmd)) := dockerTesters.map fun (pid, ev, js) =>
    (pid, (ev.map fun t => ("event", #["docker", "exec", "-i", o.container, t])).toList ++
          (js.map fun t => ("json", #["docker", "exec", "-i", o.container, t])).toList)
  procs := procs ++ [("L4YAML",
    (o.l4Event.map fun c => ("event", #[native c])).toList ++
    (o.l4Json.map fun c => ("json", #[native c])).toList)]
  let sorted := procs.toArray.qsort (fun a b => a.1 < b.1)
  let axes := if o.axis == "both" then ["event", "json"] else [o.axis]
  let rep : Reported ← IO.mkRef []
  let mut results : List (String × List (String × AxisResult)) := []
  let mut harnessErrors := 0
  for (pid, cmds) in sorted do
    if let some only := o.only then unless only.contains pid do continue
    let mut rows : List (String × AxisResult) := []
    for axis in axes do
      let some cmd := (cmds.find? (·.1 == axis)).map (·.2) | continue
      let r ← score rep cmd dirs axis o.timeoutMs o.workers
      rows := rows ++ [(axis, r)]
      harnessErrors := harnessErrors + ((r.cats.find? (·.1 == "harness-error")).map (·.2)).getD 0
      IO.eprintln (summaryLine pid axis r.cats)
    results := results ++ [(pid, rows)]
  if let some out := o.out then
    IO.FS.writeFile (underRoot o.root out) (resultsJson results)
    IO.eprintln s!"# wrote {out}"
  let reported ← rep.get
  if harnessErrors > 0 || !reported.isEmpty then
    -- a failed preflight counts even when every selected test was skipped
    IO.eprintln s!"# {harnessErrors} harness-error result(s), {reported.length} distinct harness failure(s): the harness, not a processor, failed — these scores are not publishable"
    return 1
  return 0

end Scripts.MatrixScore

public def main (args : List String) : IO UInt32 := Scripts.MatrixScore.cli args

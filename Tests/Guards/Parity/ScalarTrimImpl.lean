module

public import L4YAML.Scanner.IndexedScanner

public meta import L4YAML.Scanner.IndexedScanner
@[expose] public section Blanket

/-! # Parity of the `implemented_by` scalar trims with their `List Char` specs

`trimTrailingWSIx`, `stripTrailingNewlines` and `takeCharsIx` are defined over
`List Char` for the proofs and run through `*Impl` bodies that walk back from
the end of the string.  `#guard` evaluates with the compiler, so calling the
spec-named function here exercises the `Impl`; the right-hand sides restate the
`List Char` bodies literally.  Every string of length ≤ 5 over an alphabet that
mixes the trimmed characters (space, tab, line feed), a plain ASCII letter and
a two-byte character is checked, so byte/char offsets are exercised too. -/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates

def trimParityAlphabet : List Char := [' ', '\t', '\n', 'a', 'é']

def trimParityStrings : Nat → List String
  | 0     => [""]
  | n + 1 =>
    let shorter := trimParityStrings n
    shorter ++ (shorter.filter (·.length == n)).flatMap
      fun s => trimParityAlphabet.map s.push

#guard (trimParityStrings 5).length == 3906

#guard (trimParityStrings 5).all fun s =>
  trimTrailingWSIx s
    == String.ofList ((s.toList.reverse.dropWhile isWhiteSpaceBool).reverse)
  && trimTrailingWSIxImpl s
    == String.ofList ((s.toList.reverse.dropWhile isWhiteSpaceBool).reverse)

#guard (trimParityStrings 5).all fun s =>
  stripTrailingNewlines s
    == String.ofList ((s.toList.reverse.dropWhile isLineFeedBool).reverse)
  && stripTrailingNewlinesImpl s
    == String.ofList ((s.toList.reverse.dropWhile isLineFeedBool).reverse)

#guard (trimParityStrings 5).all fun s =>
  (List.range 7).all fun n =>
    takeCharsIx s n == String.ofList (s.toList.take n)
    && takeCharsIxImpl s n == String.ofList (s.toList.take n)

#guard trimTrailingWSIx "a \t" == "a"
#guard trimTrailingWSIx " \t" == ""
#guard trimTrailingWSIx "a \n " == "a \n"
#guard stripTrailingNewlines "a\n\n" == "a"
#guard stripTrailingNewlines "a\n \n" == "a\n "
#guard takeCharsIx "héllo  " 5 == "héllo"
#guard takeCharsIx "ab" 7 == "ab"

end L4YAML.Scanner.Indexed

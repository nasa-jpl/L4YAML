# L4YAML Tools

This directory contains analysis tools that operate on the L4YAML environment.

| Tool | Description |
|------|-------------|
| `AnalyzeThms.lean` | Theorem coverage analyzer |
| `ExtractDepGraph.lean` | Declaration dependency graph extractor |
| `ExtractSpecExamples.lean` | YAML spec example extractor |

## Theorem Dependency Graphs (TheoremGraph)

The `theoremgraph` tool has moved to the
[L4YAML.FGM](https://github.jpl.nasa.gov/pass/L4YAML.FGM) bridge project,
which combines L4YAML with the [FGM](https://github.jpl.nasa.gov/pass/FGM)
(Fibration Gap Metric) library for bipartite proof-to-code traceability analysis.

To generate theorem dependency graphs:

```bash
cd ../L4YAML.FGM
lake build theoremgraph
lake exe theoremgraph --list
lake exe theoremgraph tmp/graphs
```

The L4YAML CI pipeline automatically downloads pre-built SVG graphs from
the `graphs-latest` release of L4YAML.FGM.

# CackleX bundle, 19 September 2026

Two projects from one working session.

## shapescore/  (module ShapesCore, codename CackleX)

Lean 4.33.1, no dependencies. `lake build`; `lake env lean Audit.lean` prints
the axioms behind the main theorems. 107 theorems, about 2277 lines, no
`sorry`, `partial`, `axiom` or `native_decide`.

- README.md            what is proved, module by module, and what is not done
- PAPERS.md            sources, with how much of each was read
- DESIGN-NOTES.md      where SHACL and ShEx differ; claims tied to sources
- ARCHITECTURE.md      the generic solver (FinOp) and its use across Factoidal
- THEOREMS-FOR-SPEED.md  which theorem licenses which optimisation (frame,
                       append, certificates), and what to prove next
- FACTOIDAL-PLAN.md    placement in danbri/factoidal and the gates for replacing
                       the separate SHACL and ShEx treatments
- ShapesCore/          Graph, Syntax, Semantics, Fixpoint, Duality, SSL,
                       Frontends, CountingAsTE, Exec, Iterate, Schema,
                       Certificate, Termination, Generic, Rules, Frame, Examples,
                       ExamplesExec
- js/                  draft FP JavaScript mirror of the common core, 11 tests
                       (`node --test` in that directory)

## labs/shex-behaviours/

Experiment, not aimed at Factoidal's formal tree. Node.js prototype of an OO/FP language whose programs are ShEx schemas, with
behaviours bound to AssemblyScript, wasm, REST, Docker, MCP and WebMCP.
`npm install`, `npm test` (26 tests), `npm run demo`. See SPEC.md and README.md.
Not verified against the real thing: Docker (CLI stand-in only) and WebMCP
(mock of document.modelContext only).

Build outputs and dependencies are excluded: .lake, node_modules, .cache.

## Claude skills from Factoidal

`.claude/skills` is a relative symlink to `../../danbri/factoidal/skills`, so
Factoidal's skills (factoidal-lean-basics, lean4-proof-patterns,
lean4-performance, build-and-test, github-coauthor-policy, ...) load in a
Claude Code session opened on this repo. It resolves when Factoidal is
cloned as a sibling: from the directory above this one,

    git clone --depth 1 https://github.com/danbri/factoidal danbri/factoidal

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

## shex-behaviours/

Node.js prototype of an OO/FP language whose programs are ShEx schemas, with
behaviours bound to AssemblyScript, wasm, REST, Docker, MCP and WebMCP.
`npm install`, `npm test` (26 tests), `npm run demo`. See SPEC.md and README.md.
Not verified against the real thing: Docker (CLI stand-in only) and WebMCP
(mock of document.modelContext only).

Build outputs and dependencies are excluded: .lake, node_modules, .cache.

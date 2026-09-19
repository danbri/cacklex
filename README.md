# CackleX

Two projects from one working session (19 September 2026), kept together
here while they are prepared as contributions to
[danbri/factoidal](https://github.com/danbri/factoidal). The repository name
is `cracklex`; the project codename is CackleX.

| Directory | What it is | Build and test |
| --- | --- | --- |
| [`shapescore/`](shapescore/) | ShapesCore: a Lean 4 core for recursive shape languages (SHACL 1.2 and ShEx), following Ahmetaj et al., "Common Foundations for Recursive Shape Languages" (KR 2026). 107 theorems, no `sorry`, `partial`, `axiom` or `native_decide`. | `lake build`; `lake env lean Audit.lean` prints the axioms behind the main theorems |
| [`shapescore/js/`](shapescore/js/) | Draft JavaScript mirror of the common core, for differential testing against the Lean definitions. | `node --test` |
| [`shex-behaviours/`](shex-behaviours/) | Node.js prototype of an object-oriented and functional language whose programs are ShEx schemas. Behaviours are attached to shapes and bound to AssemblyScript, wasm, REST, Docker, MCP and WebMCP. | `npm install && npm test`; `npm run demo` |

[`MANIFEST.md`](MANIFEST.md) lists every file. Build outputs (`.lake`,
`node_modules`, `.cache`) are not committed.

## Requirements

- Lean 4.33.1 through [elan](https://github.com/leanprover/elan). The
  `shapescore/lean-toolchain` file pins the version; `lake` fetches it. No
  Mathlib and no other Lean dependencies.
- Node 20 or later for `shex-behaviours` and the JavaScript mirror.
- Docker is optional. Without a daemon the Docker binding runs against the
  CLI stand-in in `shex-behaviours/examples/services/fake-docker.mjs`.

## Verification status

Checked on 19 September 2026 on a fresh Linux container:

- `lake build` completes with zero warnings on a from-scratch build.
- The axiom audit matches [`shapescore/README.md`](shapescore/README.md):
  the constructive theorems use no axioms; the classical ones use only
  `propext`, `Classical.choice` and `Quot.sound`.
- Factoidal's escape-hatch audit (`tools/lean-hygiene-audit.py`) accepts
  the ShapesCore build log.
- JavaScript mirror: 11 of 11 tests pass.
- shex-behaviours: 26 of 26 tests pass; the demo runs every binding; the
  wasm examples rebuild byte-identically from `examples/wasm-src/`.

Not verified: the Docker binding against a real daemon, and WebMCP beyond
a mock of `document.modelContext`. Both are stated in
[`shex-behaviours/README.md`](shex-behaviours/README.md).

## Relation to Factoidal

ShapesCore is written to Factoidal's Lean rules: same toolchain, no
dependencies, no escape hatches. The intended placement is
`formal/lean4/L4Factoidal/ShapesCore/`, replacing the separate SHACL and
ShEx satisfaction engines behind their existing parsers. The route, with
the gates each stage must pass in CI, is in
[`shapescore/FACTOIDAL-PLAN.md`](shapescore/FACTOIDAL-PLAN.md). Where the
two languages differ and what follows for the core is in
[`shapescore/DESIGN-NOTES.md`](shapescore/DESIGN-NOTES.md).

shex-behaviours is a language-design prototype. It validates through
shex.js, not through Factoidal's Lean ShEx engine, so under Factoidal's
rule against hand-written reimplementations it belongs in `experiments/`
or in its own repository, not in the formal tree.

`.claude/skills` is a relative symlink to Factoidal's `skills/` directory.
It resolves when Factoidal is cloned as a sibling checkout (see
`MANIFEST.md`), so the Factoidal Lean and repository skills load in a
Claude Code session opened here.

## Licence

shex-behaviours is MIT (see its `package.json`). ShapesCore has no licence
file yet; Factoidal is Apache-2.0, and a contribution there would take that
licence.

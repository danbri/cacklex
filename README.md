# CackleX

Two projects from one working session (19 September 2026), kept together
here while they are prepared as contributions to
[danbri/factoidal-core](https://github.com/danbri/factoidal-core). The
repository is [danbri/cacklex](https://github.com/danbri/cacklex); the
project codename is CackleX. A browser demo of the JavaScript mirror is
served from [`docs/`](docs/) at <https://danbri.github.io/cacklex/>.

| Directory | What it is | Build and test |
| --- | --- | --- |
| [`shapescore/`](shapescore/) | ShapesCore: a Lean 4 core for recursive shape languages (SHACL 1.2 and ShEx), following Ahmetaj et al., "Common Foundations for Recursive Shape Languages" (KR 2026). 107 theorems, no `sorry`, `partial`, `axiom` or `native_decide`. | `lake build`; `lake env lean Audit.lean` prints the axioms behind the main theorems |
| [`shapescore/js/`](shapescore/js/) | Draft JavaScript mirror of the common core, for differential testing against the Lean definitions. | `node --test` |
| [`docs/`](docs/) | Browser demo of the mirror, published by GitHub Pages from this folder on `main`. `docs/shapes-core.mjs` is a copy of the tested mirror; CI fails if the two differ. | `cp shapescore/js/shapes-core.mjs docs/` after changing the mirror |
| [`labs/shex-behaviours/`](labs/shex-behaviours/) | Node.js prototype of an object-oriented and functional language whose programs are ShEx schemas. Behaviours are attached to shapes and bound to AssemblyScript, wasm, REST, Docker, MCP and WebMCP. | `npm install && npm test`; `npm run demo` |

[`MANIFEST.md`](MANIFEST.md) lists every file. Build outputs (`.lake`,
`node_modules`, `.cache`) are not committed.

## Requirements

- Lean 4.33.1 through [elan](https://github.com/leanprover/elan). The
  `shapescore/lean-toolchain` file pins the version; `lake` fetches it. No
  Mathlib and no other Lean dependencies.
- Node 20 or later for `shex-behaviours` and the JavaScript mirror.
- Docker is optional. Without a daemon the Docker binding runs against the
  CLI stand-in in `labs/shex-behaviours/examples/services/fake-docker.mjs`.

## Verification status

Checked on 21 October 2026 on macOS, against the tools in
`danbri/factoidal-core` at commit `f89c991` (21 October 2026):

- `lake build` completes with zero warnings on a from-scratch build
  (Lean 4.33.1, the toolchain `factoidal-core/formal/lean4` pins).
- The axiom audit matches [`shapescore/README.md`](shapescore/README.md):
  the constructive theorems use no axioms; the classical ones use only
  `propext`, `Classical.choice` and `Quot.sound`.
- `tools/lean-hygiene-audit.py` run over the ShapesCore sources and the
  audit output reports clean: no `sorry`, user `axiom`, `native_decide`,
  `unsafe`, `@[implemented_by]` or `partial def`, and every `#print axioms`
  line within the allowed three.
- `tools/lean-tail-recursion-audit.py` over the compiled IR finds no
  recursion that is not compiled to a loop (0 findings, exit 0).
- `tools/lean-csimp-reach.py` has nothing to check: ShapesCore has no
  `@[csimp]` theorem.
- JavaScript mirror: 11 of 11 tests pass.
- shex-behaviours: 26 of 26 tests pass.

The 19 September 2026 check on a fresh Linux container additionally ran the
shex-behaviours demo through every binding and rebuilt the wasm examples
byte-identically from `examples/wasm-src/`; those two were not repeated.

Not verified: the Docker binding against a real daemon, and WebMCP beyond
a mock of `document.modelContext`. Both are stated in
[`labs/shex-behaviours/README.md`](labs/shex-behaviours/README.md).

## Relation to Factoidal

Factoidal split in October 2026. The source (the F\* and Lean 4 trees,
tests, tools, skills) is now
[danbri/factoidal-core](https://github.com/danbri/factoidal-core); binaries
are built from it by `danbri/factoidal-builds`; the original
[danbri/factoidal](https://github.com/danbri/factoidal) keeps the full
history and the issue tracker. Everything below refers to factoidal-core.

ShapesCore is written to factoidal-core's Lean rules: same toolchain, no
dependencies, no escape hatches, and it passes the three audits listed
above. The intended placement is `formal/lean4/L4Factoidal/ShapesCore/`,
replacing the separate SHACL and ShEx satisfaction engines behind their
existing parsers. The route, with the gates each stage must pass, is in
[`shapescore/FACTOIDAL-PLAN.md`](shapescore/FACTOIDAL-PLAN.md). Where the
two languages differ and what follows for the core is in
[`shapescore/DESIGN-NOTES.md`](shapescore/DESIGN-NOTES.md).

`labs/` holds experiments that are not aimed at factoidal-core's formal
tree. shex-behaviours is a language-design prototype. It validates through
shex.js, not through the Lean ShEx engine, so under the rule against
hand-written reimplementations it stays under `labs/` here. factoidal-core
has no `experiments/` directory (the old repository's `experiments/` was
not carried over), so there is no home for it there.

`.claude/skills` is a relative symlink to factoidal-core's `skills/`
directory. It resolves when factoidal-core is cloned as a sibling checkout
(see `MANIFEST.md`), so the Factoidal Lean and repository skills load in a
Claude Code session opened here.

## Licence

shex-behaviours is MIT (see its `package.json`). ShapesCore has no licence
file yet; factoidal-core is Apache-2.0, and a contribution there would take
that licence.

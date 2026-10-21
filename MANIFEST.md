# CackleX bundle, 19 September 2026 (updated 21 October 2026)

Two projects from one working session, plus a browser demo.

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

## docs/

Browser demo of the JavaScript mirror, served by GitHub Pages from this
folder on `main` at https://danbri.github.io/cacklex/ (GitHub only offers
`/` or `/docs` as the folder, which is why it is not `site/`).

- index.html          the demo page
- shapes-core.mjs     a copy of shapescore/js/shapes-core.mjs; refresh it
                      with `cp` after changing the mirror. The workflow in
                      .github/workflows/site.yml runs the mirror's tests and
                      fails when the copy differs
- .nojekyll           serve the folder as-is

Build outputs and dependencies are excluded: .lake, node_modules, .cache.

## Claude skills from factoidal-core

`.claude/skills` is a relative symlink to `../../danbri/factoidal-core/skills`,
so the Factoidal skills (factoidal-lean-basics, lean4-proof-patterns,
lean4-performance, build-and-test, github-coauthor-policy, ...) load in a
Claude Code session opened on this repo. It resolves when factoidal-core is
cloned as a sibling: from the directory above this one,

    git clone --depth 1 https://github.com/danbri/factoidal-core danbri/factoidal-core

Before October 2026 the link pointed at `danbri/factoidal`, which has since
been split; its `skills/` directory moved to factoidal-core.

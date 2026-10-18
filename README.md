# On Computable Flows: public artifacts

This repository is the public, permanent home of the machine-checkable artifacts
behind the paper *On Computable Flows* (Lindsay Rex, self-published; the manuscript
itself is archived on Zenodo, which is the canonical citation for the text). It
contains the Lean 4 formalisation of the paper's novel results and the experiment
code and frozen run artifacts that every number printed in the paper comes from.
It does not contain the manuscript sources or the research working notes; those
live in a private research repository, and every file here is a byte-identical
copy of a committed file there (see Provenance below).

## Layout

| Path | Contents |
| --- | --- |
| `lean_verification/` | Lean 4 + Mathlib formalisation of the paper's novel results. `MAP.md` maps each paper result to its Lean declarations and states exactly what each file does and does not formalise. |
| `v3/exp_007_deconvolution/` | The deblurring experiment: frozen method brief, source, results, run manifest. Source of the certified-versus-measured numbers in the worked-examples section. |
| `v3/exp_008_lorenz_construction/` | The constructed-chaos experiment (Lorenz family and coupled lattice): frozen brief with registered amendments, source, results, run manifest. Source of the dynamic-null and synchronisation-threshold numbers. |
| `experiments/rule110_flow/` | The Rule 110 construction: code, claims ledger, summary. Source of the computability section's table. |
| `v5/figures/` | Witness scripts. Each renders a paper figure from the committed result files only and prints every number the paper cites from it. |
| `v3/pyproject.toml`, `v3/uv.lock` | The pinned Python environment the experiments ran under. |
| `EXPORT_MANIFEST.txt` | Source commit and sha256 of every file here. |

## Checking the Lean

The formalisation covers the paper's novel results only; classical results are
cited in the paper against textbook locators and are not re-proved, in prose or
in Lean. `lean_verification/MAP.md` is the scope document: for each result it
names the Lean declarations and lists what remains prose-only.

To build (the toolchain is pinned in `lean_verification/lean-toolchain`):

```sh
cd lean_verification
lake exe cache get   # fetch the Mathlib build cache
lake build
```

A clean build with no `sorry` is what the paper's Lean pointers claim; the CI
badge on this repository reports the same build.

## Rerunning the experiments

Each experiment directory follows one scheme: `experiment/exp_method.md` is the
method brief, frozen and committed before any computation, with amendments
registered in place; `src/` is the code; `results/` holds the outputs the paper
reads; `runs/run_manifest.json` records the resolved environment of the actual
runs. The environment is recreated from the lock file:

```sh
cd v3 && uv sync
uv run python exp_008_lorenz_construction/src/run_calibration.py   # for example
```

The witness scripts need only the committed result files:

```sh
uv run python ../v5/figures/make_lorenz_ramp.py
```

## Provenance

`EXPORT_MANIFEST.txt` names the source commit of the private research repository
and the sha256 of every file. Files are exported allowlist-only by a script that
copies committed files unmodified, so each hash here equals the hash of the same
path at that commit. Nothing in this repository is edited after export.

## License

Apache License 2.0 (see `LICENSE`), matching Mathlib's license for the Lean code.

## Citing

See `CITATION.cff`. For the paper's text, cite the Zenodo record of the
manuscript; for the artifacts, this repository (a Zenodo DOI for tagged releases
of this repository is planned).

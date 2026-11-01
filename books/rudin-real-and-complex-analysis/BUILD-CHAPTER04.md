# Chapter 4 build and axiom evidence

The module covers the 26 printed nodes 4.1–4.26, with the explicit corrections
in [SCOPING-B.md](SCOPING-B.md) and declaration map in
[CHAPTER04-COVERAGE.md](CHAPTER04-COVERAGE.md). This is implementation evidence;
the coordinator's independent crossed review is still required.

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Clean gate began: `2026-11-01T09:05:21.675956+00:00`.
- Clean gate finished: `2026-11-01T09:09:48.983732+00:00`.
- The entire old `.lake` directory was moved outside the book. No prior project
  build artifact or incremental snapshot was used in this gate.
- Fresh `lake exe cache get`: exit **0**; ordinary `lake build`: exit **0**.
- Serialized with the lane-local lock, `LEAN_NUM_THREADS=1` for Lake, and
  `weakLeanArgs = ["-j1"]` in `lakefile.toml` for chapter compiler invocations.
  The environment variable alone does not force the chapter compiler to use `-j1`.
- Axiom allowlist checker: exit **0**, rerun against this source and the full build log.
- Every theorem/lemma has a `#print axioms` command: **172 declarations,
  172 audit records, zero missing records, zero disallowed axioms**.
- Observed axiom union: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, added `axiom`, or `native_decide` occurs in the module.
- Chapter04 source SHA256: `d71fb2f7202629914f1773382b9a8448c462a29d27fc1ff300ff8f17100c4b45`.
- Lake configuration SHA256: `5891835867714a57568c217bcae78911549ea06bd0896de174d2bdb13eeab5b6`.

The [fresh cache-fetch log](evidence/chapter04-clean-continuation2-cache.log),
[full clean-build log](evidence/chapter04-clean-continuation2-build.log),
[audit summary](evidence/chapter04-clean-continuation2-Chapter04-axioms.log), and
[clean-gate metadata](evidence/chapter04-clean-metadata.json) are included.
The dependency cache is the pinned upstream Mathlib cache; it contains no
prebuilt copy of this new chapter module.

# Preservation: brooklynn home-root 2026-11-12

Source: `/root/coincidence-mining` on brooklynn (100.124.8.33), 51M,
flagged as a home-root conformance violation in the 2026-11-12 daily run.

## What this is

OEIS coincidence-mining research, run Oct 22–24, 2026 (Argon judge):
shard analysis over 6,250 OEIS records (2,052 families), stress tests,
a live judge packet with evidence, a litcheck verdict and a recompute.
`run.log`: "shard: 2052 families, 6250 records / records fetched:
6250/6250 / finalists=914 known=894 stated=61".

## What is preserved here (6.2M, 466 files)

The unique work product: analysis scripts, shard/stress outputs and
logs, `judge/` (finalist packet + Argon judge report), the
`judge-live-20261023/` packet (PACKET2-FULL.md, JUDGE-LIVE.md,
judge-evidence/), `litcheck-argon-20261024/` (VERDICT.md) and
`recompute-argon-20261024/` (recompute.py + results).

## What is NOT preserved here — and why

- `records/` (~27M, ~6,000 `A*.seq` files): raw OEIS sequence files,
  reproducible by re-fetching from oeis.org. Not unique work.
- `judge-live-20261023/.firecrawl/`: scraper cache, regenerable.

Both were left out deliberately; the full 51M tree was moved intact
to `/root/projects/coincidence-mining` on brooklynn after this PR
opened, so nothing was deleted. This PR preserves the unique outputs
independently of that machine.

Scanned 2026-11-12: no credential-like strings in the preserved files.

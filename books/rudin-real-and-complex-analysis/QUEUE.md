# Queue — stuck nodes

Nothing here is silently dropped. A node leaves this file only after a
faithful proof or a coordinator ruling recorded on its ticket.

## 3.7 — essential supremum at zero measure (fidelity hold)

The printed third-edition pp.65–66 define the threshold set using **all real
α**, even for nonnegative functions. With the zero measure on a singleton
and the zero function, every real threshold belongs to the set. It is
unbounded below, so the stated real infimum does not exist; an extended-real
interpretation gives minus infinity rather than a nonnegative norm.

Evidence and scan links: [Chapter 3 inventory](INVENTORY-CH03.md).
`RudinRCA/Chapter03.lean` records the counterexample and an explicitly
labelled correction using nonnegative extended thresholds. The original
node remains held; no downstream node is counted complete using an
unannounced correction. Coordinator ruling is pending.

# books/

One directory per book, named by a lowercase-hyphen slug (e.g. `rudin-real-and-complex-analysis/`). Each is a self-contained Lake project:

```
books/<slug>/
  lakefile.toml     (or lakefile.lean)
  lean-toolchain    Lean 4.34.1 — pinned; never float mid-book
  <Book>/           the formalization sources, one file per chapter
  <Book>.lean       imports all chapters
  PROGRESS.md       per-chapter node counts (done / total)
  QUEUE.md          stuck nodes and what's blocking them
```

Before starting a book, add its row to `../CATALOGUE.md` with the landscape check.

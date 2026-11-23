# lean-proofs

Lean 4 / mathlib formalizations of undergraduate mathematics, written with mathlib conventions
(docstrings, `namespace`, mathlib linter settings).

| File | Content |
|------|---------|
| `LeanProofs/Basic.lean` | Closed forms of finite sums (Gauss sum, odd numbers, sum of squares) |
| `LeanProofs/Inequalities.lean` | Bernoulli, AM-GM (two variables), Cauchy–Schwarz in dimension 2 |

## Build

```bash
lake exe cache get
lake build
```

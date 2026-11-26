![Lean Action CI](https://github.com/elsasc1/lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)
# lean-proofs

Lean 4 / mathlib formalizations of undergraduate mathematics, written with mathlib conventions
(docstrings, `namespace`, mathlib linter settings).

| File | Content |
|------|---------|
| `LeanProofs/Basic.lean` | Closed forms of finite sums (Gauss sum, odd numbers, sum of squares) |
| `LeanProofs/Inequalities.lean` | Bernoulli, AM-GM (two variables), Cauchy–Schwarz in dimension 2 |
| `LeanProofs/BinomialModel.lean` | One-period binomial (CRR) model: no-arbitrage ⇔ `d < R < u` ⇔ risk-neutral probability in `(0,1)`; replication and pricing formula |

## Build

```bash
lake exe cache get
lake build
```

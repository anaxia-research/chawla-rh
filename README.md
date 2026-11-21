# The Liouville Function, the Riemann Hypothesis and Chowla's Conjecture

Lean 4 / Mathlib formalisation.

## What is proved

| Statement | Where | Status |
|---|---|---|
| `λ = σ * μ`, `σ = λ * 1` is the indicator of squares | `ChowlaRH/SquareKernel.lean` | Lean, unconditional |
| `|M(N)| ≤ C N^θ` (θ > 1/2) ⟹ `|L(N)| ≤ C ζ(2θ) N^θ` | `ChowlaRH/MertensTransfer.lean` | Lean, unconditional |
| `L(N) ≪ N^θ` (θ < 1) ⟹ one-point Chowla for every shift | `ChowlaRH/Chowla.lean` | Lean, unconditional |
| `LittlewoodRH` ⟹ Chowla of order 1 | `ChowlaRH/Chowla.lean` | Lean, hypothesis `LittlewoodRH` |
| Correlations on all subsets ⟹ every sign pattern has density `2^-k` (any positive weights) | `ChowlaRH/SignPatterns.lean` | Lean, unconditional |
| Full Chowla ⟹ all sign patterns equidistributed | `ChowlaRH/SignPatterns.lean` | Lean |
| Tao (k=2, log) + Tao–Teräväinen (odd k, log) ⟹ all patterns of length ≤ 3 have log density `2^-k` | `ChowlaRH/SignPatterns.lean` | Lean, cited theorems as named hypotheses |
| Averaged Chowla (Matomäki–Radziwiłł–Tao) ⟹ for all but δH^k tuples h ∈ [1,H]^k, every sign pattern has frequency within δ of 2^-k | `ChowlaRH/AlmostAll.lean` | Lean, cited theorem as named hypothesis `MRTAveraged` |
| RH ⟺ `M(x) ≪ x^{1/2+ε}` ⟺ `L(x) ≪ x^{1/2+ε}` | accompanying paper, §3 | paper proof (Perron formula not in Mathlib) |
| GRH ⟹ `λ` in progressions `≪ q^ε x^{1/2+ε}` | accompanying paper, §4 | paper proof |

Chowla's conjecture of order k ≥ 2 (Cesàro averages), and its logarithmic form for even k ≥ 4,
are **not** proved here and are not known to follow from RH or GRH. See §7 of the paper.

## Hypotheses

* `LittlewoodRH : ∀ ε > 0, MertensBound (1/2 + ε)` — equivalent to RH (paper, Theorem 1.2).
* `TaoTwoPoint`, `TaoTeravainenOdd`, `MRTAveraged` — published theorems (Forum Math. Pi 2016; JTNB 2018, Duke 2019; Algebra Number Theory 2015),
  stated in the notation of the development.

No hypothesis is used anywhere except as an explicit argument.

## Build

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

`axioms.txt` holds the `#print axioms` output: every theorem uses only
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `axiom`, no `native_decide`.

Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.

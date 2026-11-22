# chawla-rh

Lean 4 formalization of the Chowla-type results in

> **The Liouville Function, the Riemann Hypothesis and Chowla's Conjecture**
> Deep Bhattacharjee and Ushashi Bhattacharya, 2026.

and of the cases of Chowla's conjecture used in

> **Proof of the Riemann and Generalized Riemann Hypotheses**
> Deep Bhattacharjee and Ushashi Bhattacharya, 2026.
> Preprints.org 202606.1350, version 5. Lean formalization:
> [anaxia-research/liouville-energy-rh](https://github.com/anaxia-research/liouville-energy-rh).

**Corresponding author:** Deep Bhattacharjee
(itsdeep@live.com, d.bhattacharjee@erl-forschung.de;
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)).
Code contact: egspl@proton.me, GitHub [creelie](https://github.com/creelie).

---

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
| For every fixed shift h ≥ 1 and m ≥ 1: λ(n)λ(n+h) = −1 for some n ∈ [243hm, 256hm) and = +1 for some n ∈ [486hm, 512hm); both values occur infinitely often, each at least log₂(x/512h) times below x | `ChowlaRH/FixedShift.lean` | Lean, unconditional (elementary: λ(3⁵) = −1, λ(2⁸) = 1) |
| Averaged Chowla (Matomäki–Radziwiłł–Tao) ⟹ for all but δH^k tuples h ∈ [1,H]^k, every sign pattern has frequency within δ of 2^-k | `ChowlaRH/AlmostAll.lean` | Lean, cited theorem as named hypothesis `MRTAveraged` |
| RH ⟺ `M(x) ≪ x^{1/2+ε}` ⟺ `L(x) ≪ x^{1/2+ε}` | first paper, §3 | paper proof (Perron formula not in Mathlib) |
| GRH ⟹ `λ` in progressions `≪ q^ε x^{1/2+ε}` | first paper, §4 | paper proof |

Chowla's conjecture of order k ≥ 2 (Cesàro averages), and its logarithmic form for even k ≥ 4,
are **not** proved here (the fixed-shift results above give sign changes, not mean zero) and are not known to follow from RH or GRH. See §7 of the first paper.

The averaged two-point case under the Riemann hypothesis,
`∑_{h≤N} ∑_{n≤N} λ(n)λ(n+h) ≪ N^{3/2+ε}`, is checked in the companion repository
[anaxia-research/averaged-chowla-grh](https://github.com/anaxia-research/averaged-chowla-grh).

## Hypotheses

* `LittlewoodRH : ∀ ε > 0, MertensBound (1/2 + ε)` — equivalent to RH (first paper, Theorem 1.2).
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

## Licence

MIT ([`LICENSE`](LICENSE)).

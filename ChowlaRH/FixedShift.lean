/-
Fixed-shift correlations of the Liouville function: unconditional sign results.

For every fixed shift `h ≥ 1` the product `λ(n) λ(n + h)` takes the value `-1`
in every interval `[243 h m, 256 h m)` and the value `+1` in every interval
`[486 h m, 512 h m)`.  Consequently both values occur infinitely often, and each
occurs at least `k` times below `512 h 2^k`.  The proofs use only complete
multiplicativity and the identities `λ(3^5) = -1`, `λ(2^8) = 1`.
-/
import Mathlib

open ArithmeticFunction Finset

namespace ChowlaRH

theorem liouville_sq_eq_one {n : ℕ} (hn : n ≠ 0) : liouville n * liouville n = 1 := by
  rw [liouville_apply hn, ← pow_add, ← two_mul, pow_mul]
  simp

theorem liouville_eq_or {n : ℕ} (hn : n ≠ 0) : liouville n = 1 ∨ liouville n = -1 := by
  rw [liouville_apply hn]
  exact neg_one_pow_eq_or ℤ _

theorem liouville_243 : liouville 243 = -1 := by
  rw [show (243 : ℕ) = 3 ^ 5 by norm_num, liouville_apply (by norm_num),
    cardFactors_apply_prime_pow Nat.prime_three]
  norm_num

theorem liouville_256 : liouville 256 = 1 := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, liouville_apply (by norm_num),
    cardFactors_apply_prime_pow Nat.prime_two]
  norm_num

/-- A walk with step `h` whose endpoints carry different Liouville values has a
step at which the value changes. -/
theorem exists_change (x h : ℕ) :
    ∀ L : ℕ, liouville x ≠ liouville (x + L * h) →
      ∃ j < L, liouville (x + j * h) ≠ liouville (x + j * h + h) := by
  intro L
  induction L with
  | zero => intro hne; simp at hne
  | succ L ih =>
    intro hne
    by_cases hL : liouville x = liouville (x + L * h)
    · refine ⟨L, Nat.lt_succ_self L, ?_⟩
      rw [← hL]
      simpa [Nat.succ_mul, add_assoc] using hne
    · obtain ⟨j, hj, hj'⟩ := ih hL
      exact ⟨j, Nat.lt_succ_of_lt hj, hj'⟩

/-- An alternating walk returns to its starting value after an even number of steps. -/
theorem alternating_walk (x h : ℕ) :
    ∀ L : ℕ, (∀ j < L, liouville (x + j * h + h) = -liouville (x + j * h)) →
      liouville (x + L * h) = (-1) ^ L * liouville x := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hstep
    have h1 := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have h2 := hstep L (Nat.lt_succ_self L)
    rw [show x + (L + 1) * h = x + L * h + h by ring, h2, h1, pow_succ]
    ring

theorem mul_eq_neg_one_of_ne {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : liouville a ≠ liouville b) : liouville a * liouville b = -1 := by
  rcases liouville_eq_or ha with h1 | h1 <;> rcases liouville_eq_or hb with h2 | h2 <;>
    simp_all

/-- **Theorem A.** For every shift `h ≥ 1` and every `m ≥ 1` there is
`n ∈ [243 h m, 256 h m)` with `λ(n) λ(n + h) = -1`. -/
theorem exists_neg_in_window {h m : ℕ} (hh : 0 < h) (hm : 0 < m) :
    ∃ n, 243 * h * m ≤ n ∧ n < 256 * h * m ∧ liouville n * liouville (n + h) = -1 := by
  have hhm : h * m ≠ 0 := by positivity
  have hne : liouville (243 * h * m) ≠ liouville (243 * h * m + 13 * m * h) := by
    rw [show 243 * h * m + 13 * m * h = 256 * (h * m) by ring,
      show 243 * h * m = 243 * (h * m) by ring, liouville_apply_mul 243 (h * m),
      liouville_apply_mul 256 (h * m), liouville_243, liouville_256]
    intro heq
    have h0 := liouville_ne_zero hhm
    have : liouville (h * m) = 0 := by linarith
    exact h0 this
  obtain ⟨j, hj, hj'⟩ := exists_change (243 * h * m) h (13 * m) hne
  refine ⟨243 * h * m + j * h, Nat.le_add_right _ _, ?_, ?_⟩
  · have : j * h < 13 * m * h := Nat.mul_lt_mul_of_pos_right hj hh
    nlinarith
  · exact mul_eq_neg_one_of_ne (by positivity) (by positivity) hj'

/-- **Theorem B.** For every shift `h ≥ 1` and every `m ≥ 1` there is
`n ∈ [486 h m, 512 h m)` with `λ(n) λ(n + h) = 1`. -/
theorem exists_pos_in_window {h m : ℕ} (hh : 0 < h) (hm : 0 < m) :
    ∃ n, 486 * h * m ≤ n ∧ n < 512 * h * m ∧ liouville n * liouville (n + h) = 1 := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j < 26 * m, liouville (486 * h * m + j * h + h) =
      -liouville (486 * h * m + j * h) := by
    intro j hj
    have hn0 : 486 * h * m + j * h ≠ 0 := by positivity
    have hlt : 486 * h * m + j * h < 512 * h * m := by
      have : (j + 1) * h ≤ 26 * m * h := Nat.mul_le_mul_right _ hj
      nlinarith
    have hp := hcon _ (Nat.le_add_right _ _) hlt
    rcases liouville_eq_or hn0 with h1 | h1 <;>
      rcases liouville_eq_or (show 486 * h * m + j * h + h ≠ 0 by positivity) with h2 | h2 <;>
      rw [h1, h2] at hp ⊢ <;> simp at hp ⊢
  have hw := alternating_walk (486 * h * m) h (26 * m) hstep
  rw [show 486 * h * m + 26 * m * h = (2 * h) * (256 * m) by ring,
    show (-1 : ℤ) ^ (26 * m) = 1 by rw [pow_mul]; norm_num, one_mul,
    show 486 * h * m = (2 * h) * (243 * m) by ring, liouville_apply_mul (2 * h) (256 * m),
    liouville_apply_mul (2 * h) (243 * m), liouville_apply_mul 256 m,
    liouville_apply_mul 243 m, liouville_243, liouville_256] at hw
  have h2h := liouville_ne_zero (show 2 * h ≠ 0 by positivity)
  have hm0 := liouville_ne_zero (show m ≠ 0 by positivity)
  have : liouville (2 * h) * liouville m = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact h2h h'
  · exact hm0 h'

/-- Both values of `λ(n) λ(n + h)` occur infinitely often, for every fixed `h ≥ 1`. -/
theorem infinite_neg {h : ℕ} (hh : 0 < h) :
    {n : ℕ | liouville n * liouville (n + h) = -1}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn1, -, hn3⟩ := exists_neg_in_window hh (Nat.succ_pos a)
  exact ⟨n, hn3, by nlinarith⟩

theorem infinite_pos {h : ℕ} (hh : 0 < h) :
    {n : ℕ | liouville n * liouville (n + h) = 1}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn1, -, hn3⟩ := exists_pos_in_window hh (Nat.succ_pos a)
  exact ⟨n, hn3, by nlinarith⟩

/-- Counting lemma: points chosen in the windows `[c·2^i, d·2^i)` with `d ≤ 2c` are
distinct, so `k` windows below `d·2^k` give `k` points. -/
theorem card_ge_of_windows (P : ℕ → Prop) [DecidablePred P] {c d : ℕ} (hcd : d ≤ 2 * c)
    (hw : ∀ i : ℕ, ∃ n, c * 2 ^ i ≤ n ∧ n < d * 2 ^ i ∧ P n) (hc : 0 < c) (k : ℕ) :
    k ≤ ((Icc 1 (d * 2 ^ k)).filter P).card := by
  choose f hf1 hf2 hf3 using hw
  have hmono : StrictMono f := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    calc f i < d * 2 ^ i := hf2 i
      _ ≤ 2 * c * 2 ^ i := Nat.mul_le_mul_right _ hcd
      _ = c * 2 ^ (i + 1) := by ring
      _ ≤ f (i + 1) := hf1 (i + 1)
  have hsub : (range k).image f ⊆ (Icc 1 (d * 2 ^ k)).filter P := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hi' := mem_range.mp hi
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, hf3 i⟩
    · have : 1 ≤ c * 2 ^ i := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact le_trans this (hf1 i)
    · have : d * 2 ^ i ≤ d * 2 ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hi'.le)
      exact (hf2 i).le.trans this
  have := card_le_card hsub
  rwa [card_image_of_injective _ hmono.injective, card_range] at this

/-- **Corollary.** For every `h ≥ 1` and `k ≥ 0`, at least `k` integers
`n ≤ 256 h 2^k` have `λ(n) λ(n + h) = -1`; in particular the count up to `x`
is at least `log₂ (x / 256 h)`. -/
theorem card_neg_ge {h : ℕ} (hh : 0 < h) (k : ℕ) :
    k ≤ ((Icc 1 (256 * h * 2 ^ k)).filter
      (fun n => liouville n * liouville (n + h) = -1)).card := by
  refine card_ge_of_windows _ (c := 243 * h) (by omega) (fun i => ?_) (by positivity) k
  obtain ⟨n, h1, h2, h3⟩ := exists_neg_in_window hh (pow_pos (show 0 < 2 by norm_num) i)
  exact ⟨n, by linarith [h1], by linarith [h2], h3⟩

/-- **Corollary.** For every `h ≥ 1` and `k ≥ 0`, at least `k` integers
`n ≤ 512 h 2^k` have `λ(n) λ(n + h) = 1`. -/
theorem card_pos_ge {h : ℕ} (hh : 0 < h) (k : ℕ) :
    k ≤ ((Icc 1 (512 * h * 2 ^ k)).filter
      (fun n => liouville n * liouville (n + h) = 1)).card := by
  refine card_ge_of_windows _ (c := 486 * h) (by omega) (fun i => ?_) (by positivity) k
  obtain ⟨n, h1, h2, h3⟩ := exists_pos_in_window hh (pow_pos (show 0 < 2 by norm_num) i)
  exact ⟨n, by linarith [h1], by linarith [h2], h3⟩

end ChowlaRH

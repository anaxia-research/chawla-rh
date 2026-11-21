/-
Chowla's conjecture for almost all shifts.

From the averaged Chowla theorem of Matomäki, Radziwiłł and Tao (stated here as the named
hypothesis `MRTAveraged`), we prove: for every `k` and `δ > 0`, for all large `H` and all
large `X`, all but at most `δ H^k` of the shift tuples `h ∈ [1, H]^k` have the property that
every sign pattern `ε ∈ {±1}^k` is taken by `(λ(n + h_1), …, λ(n + h_k))`, `n ≤ X`, with
frequency within `δ` of `2^{-k}`.
-/
import ChowlaRH.SignPatterns

open ArithmeticFunction Finset Filter Topology Real

namespace ChowlaRH

noncomputable section

open Classical in
/-- The unnormalised correlation `∑_{n ≤ X} ∏_{i} λ(n + g_i + 1)` of a shift tuple
`g : ι → Fin H` (so the shifts `g_i + 1` lie in `[1, H]`). -/
def tcorr {ι : Type*} [Fintype ι] {H : ℕ} (g : ι → Fin H) (X : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 X, ∏ i, lam (n + ((g i : ℕ) + 1))

/-- Averaged Chowla of order `j`: `∑_{h ∈ [1,H]^j} |∑_{n ≤ X} ∏ λ(n + h_i)| ≤ ε H^j X`
for all large `H` and then all large `X`. -/
def AveragedChowla (j : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
    ∑ g : Fin j → Fin H, |tcorr g X| ≤ ε * (H : ℝ) ^ j * X

/-- Matomäki–Radziwiłł–Tao (Algebra Number Theory 2015): averaged Chowla of every order. -/
def MRTAveraged : Prop := ∀ j : ℕ, 1 ≤ j → AveragedChowla j

/-- Correlation along a subset `S` of the coordinates of `h`. -/
def scorr {k H : ℕ} (S : Finset (Fin k)) (h : Fin k → Fin H) (X : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 X, ∏ i ∈ S, lam (n + ((h i : ℕ) + 1))

theorem scorr_eq_tcorr {k H : ℕ} (S : Finset (Fin k)) (h : Fin k → Fin H) (X : ℕ) :
    scorr S h X = tcorr (fun s : S => h s) X := by
  unfold scorr tcorr
  refine sum_congr rfl fun n _ => ?_
  exact (prod_coe_sort S (fun i => lam (n + ((h i : ℕ) + 1)))).symm

/-- Summing a function of the restriction `h|_S` over all `h` multiplies by `H^{k - |S|}`. -/
theorem sum_restrict {k H : ℕ} (S : Finset (Fin k)) (F : (S → Fin H) → ℝ) :
    ∑ h : Fin k → Fin H, F (fun s : S => h s) =
      (H : ℝ) ^ (k - S.card) * ∑ g : S → Fin H, F g := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin k => i ∈ S) (fun _ => Fin H)
  rw [← Fintype.sum_equiv e.symm (fun p => F p.1) (fun h => F (fun s : S => h s))
    (fun p => by simp [e, Equiv.piEquivPiSubtypeProd])]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [mul_sum]
  refine sum_congr rfl fun g _ => ?_
  congr 1
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, prod_const, card_univ, Nat.cast_pow]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

/-- Relabelling the index set by `S ≃ Fin |S|`. -/
theorem sum_tcorr_relabel {k H : ℕ} (S : Finset (Fin k)) (X : ℕ) :
    ∑ g : S → Fin H, |tcorr g X| = ∑ g : Fin S.card → Fin H, |tcorr g X| := by
  let σ : S ≃ Fin S.card := S.equivFin
  refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl _)) _ _ fun g => ?_
  congr 1
  unfold tcorr
  refine sum_congr rfl fun n _ => ?_
  exact Fintype.prod_equiv σ _ _ (fun s => by simp [Equiv.arrowCongr_apply])

theorem sum_abs_scorr {k H : ℕ} (S : Finset (Fin k)) (X : ℕ) :
    ∑ h : Fin k → Fin H, |scorr S h X| =
      (H : ℝ) ^ (k - S.card) * ∑ g : Fin S.card → Fin H, |tcorr g X| := by
  simp_rw [scorr_eq_tcorr]
  rw [sum_restrict S (fun g => |tcorr g X|), sum_tcorr_relabel]

/-! ### Pattern frequencies of a tuple -/

/-- Number of `n ≤ X` with `λ(n + h_i + 1) = ε_i` for every `i`. -/
def patCount {k H : ℕ} (h : Fin k → Fin H) (ε : Fin k → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 X, if ∀ i, lam (n + ((h i : ℕ) + 1)) = ε i then 1 else 0

theorem patInd_expand {k H : ℕ} (h : Fin k → Fin H) {ε : Fin k → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (n : ℕ) :
    (if ∀ i, lam (n + ((h i : ℕ) + 1)) = ε i then (1 : ℝ) else 0) =
      (1 / 2) ^ k * ∑ S ∈ (univ : Finset (Fin k)).powerset,
        (∏ i ∈ S, ε i) * ∏ i ∈ S, lam (n + ((h i : ℕ) + 1)) := by
  have hf : ∀ i ∈ (univ : Finset (Fin k)), (1 + ε i * lam (n + ((h i : ℕ) + 1))) / 2 =
      if lam (n + ((h i : ℕ) + 1)) = ε i then 1 else 0 :=
    fun i _ => factor_eq (lam_eq_or (by omega)) (hε i)
  have hprod : (if ∀ i, lam (n + ((h i : ℕ) + 1)) = ε i then (1 : ℝ) else 0) =
      ∏ i, (1 + ε i * lam (n + ((h i : ℕ) + 1))) / 2 := by
    rw [prod_congr rfl hf]
    split_ifs with hall
    · exact (prod_eq_one fun i _ => by simp [hall i]).symm
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact (prod_eq_zero (mem_univ i) (by simp [hi])).symm
  rw [hprod, prod_div_distrib, prod_const, prod_one_add, card_univ, Fintype.card_fin]
  rw [div_eq_mul_inv, mul_comm, one_div, inv_pow]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [← prod_mul_distrib]

/-- If every nonempty sub-correlation of `h` is at most `δ X` in size, every pattern count
is within `δ X` of `2^{-k} X`. -/
theorem patCount_close {k H : ℕ} (h : Fin k → Fin H) {ε : Fin k → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (X : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ S : Finset (Fin k), S.Nonempty → |scorr S h X| ≤ δ * X) :
    |patCount h ε X - (1 / 2) ^ k * X| ≤ δ * X := by
  have hexp : patCount h ε X = (1 / 2) ^ k *
      ∑ S ∈ (univ : Finset (Fin k)).powerset, (∏ i ∈ S, ε i) * scorr S h X := by
    unfold patCount scorr
    simp_rw [patInd_expand h hε, ← mul_sum]
    rw [sum_comm]
    refine congrArg _ (sum_congr rfl fun S _ => ?_)
    rw [mul_sum]
  have hsplit := sum_erase_add ((univ : Finset (Fin k)).powerset)
    (fun S => (∏ i ∈ S, ε i) * scorr S h X) (empty_mem_powerset _)
  have hempty : (∏ i ∈ (∅ : Finset (Fin k)), ε i) * scorr ∅ h X = X := by
    simp [scorr]
  rw [hexp, ← hsplit, hempty, mul_add, add_sub_cancel_right]
  have hεS : ∀ S : Finset (Fin k), |∏ i ∈ S, ε i| = 1 := fun S => by
    rw [abs_prod]; exact prod_eq_one fun i _ => by rcases hε i with h | h <;> simp [h]
  have hbound : |∑ S ∈ (univ.powerset).erase ∅, (∏ i ∈ S, ε i) * scorr S h X| ≤
      ((2 : ℝ) ^ k) * (δ * X) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ S ∈ (univ.powerset).erase ∅, |(∏ i ∈ S, ε i) * scorr S h X|
        ≤ ∑ S ∈ ((univ : Finset (Fin k)).powerset).erase ∅, δ * X := by
          refine sum_le_sum fun S hS => ?_
          rw [abs_mul, hεS, one_mul]
          exact hgood S (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hS))
      _ ≤ ∑ S ∈ (univ : Finset (Fin k)).powerset, δ * X :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            (fun _ _ _ => mul_nonneg hδ (Nat.cast_nonneg _))
      _ = (2 : ℝ) ^ k * (δ * X) := by
          rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (1 / 2) ^ k * |∑ S ∈ (univ.powerset).erase ∅, (∏ i ∈ S, ε i) * scorr S h X|
      ≤ (1 / 2) ^ k * ((2 : ℝ) ^ k * (δ * X)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = δ * X := by rw [← mul_assoc, ← mul_pow]; norm_num

/-! ### Markov's inequality on the shift tuples -/

theorem card_filter_lt_le {α : Type*} (s : Finset α) (a : α → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    ((s.filter fun x => t < a x).card : ℝ) ≤ (∑ x ∈ s, a x) / t := by
  rw [le_div_iff₀ ht]
  calc ((s.filter fun x => t < a x).card : ℝ) * t = ∑ x ∈ s.filter (fun x => t < a x), t := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s.filter (fun x => t < a x), a x :=
        sum_le_sum fun x hx => (mem_filter.mp hx).2.le
    _ ≤ ∑ x ∈ s, a x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x hx _ => ha x hx)

open Classical in
/-- **Chowla for almost all shifts.**  Under the averaged Chowla theorem, for every `k` and
`δ > 0`, for all large `H` and then all large `X`, at most `δ H^k` tuples `h ∈ [1,H]^k`
have some sign pattern whose frequency among `n ≤ X` differs from `2^{-k}` by more than `δ`. -/
theorem almostAll_patterns (hA : MRTAveraged) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      (((univ : Finset (Fin k → Fin H)).filter fun h =>
        ∃ ε : Fin k → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
          δ < |patCount h ε X / X - (1 / 2) ^ k|).card : ℝ) ≤ δ * (H : ℝ) ^ k := by
  set η : ℝ := δ * δ / 2 ^ k with hη
  have hη0 : 0 < η := by positivity
  -- the averaged bound for every nonempty subset, eventually
  have hall : ∀ S : Finset (Fin k), ∀ᶠ H : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      S.Nonempty → ∑ g : Fin S.card → Fin H, |tcorr g X| ≤ η * (H : ℝ) ^ S.card * X := by
    intro S
    by_cases hS : S.Nonempty
    · filter_upwards [hA S.card (card_pos.mpr hS) η hη0] with H hH
      filter_upwards [hH] with X hX _ using hX
    · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ hS' => absurd hS' hS
  have hall' : ∀ᶠ H : ℕ in atTop, ∀ S : Finset (Fin k), ∀ᶠ X : ℕ in atTop,
      S.Nonempty → ∑ g : Fin S.card → Fin H, |tcorr g X| ≤ η * (H : ℝ) ^ S.card * X :=
    eventually_all.mpr hall
  filter_upwards [hall'] with H hH
  have hH' : ∀ᶠ X : ℕ in atTop, ∀ S : Finset (Fin k),
      S.Nonempty → ∑ g : Fin S.card → Fin H, |tcorr g X| ≤ η * (H : ℝ) ^ S.card * X :=
    eventually_all.mpr hH
  filter_upwards [hH', eventually_ge_atTop 1] with X hX hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  set t : ℝ := δ * X
  have ht : 0 < t := mul_pos hδ hXpos
  -- the bad set is covered by the sets where some sub-correlation exceeds δX
  have hsub : ((univ : Finset (Fin k → Fin H)).filter fun h =>
        ∃ ε : Fin k → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
          δ < |patCount h ε X / X - (1 / 2) ^ k|) ⊆
      ((univ : Finset (Finset (Fin k))).filter Finset.Nonempty).biUnion
        (fun S => (univ : Finset (Fin k → Fin H)).filter fun h => t < |scorr S h X|) := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    obtain ⟨ε, hε, hbad⟩ := hh
    by_contra hcon
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and,
      not_lt] at hcon
    have hclose := patCount_close h hε X hδ.le (fun S hS => hcon S hS)
    have : |patCount h ε X / X - (1 / 2) ^ k| ≤ δ := by
      rw [show patCount h ε X / X - (1 / 2) ^ k = (patCount h ε X - (1 / 2) ^ k * X) / X by
        field_simp, abs_div, abs_of_pos hXpos, div_le_iff₀ hXpos]
      exact hclose
    linarith
  calc _ ≤ (((((univ : Finset (Finset (Fin k))).filter Finset.Nonempty).biUnion
        (fun S => (univ : Finset (Fin k → Fin H)).filter fun h => t < |scorr S h X|)).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin k))).filter Finset.Nonempty,
          (((univ : Finset (Fin k → Fin H)).filter fun h => t < |scorr S h X|).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin k))).filter Finset.Nonempty,
          η * (H : ℝ) ^ k / δ := by
        refine sum_le_sum fun S hS => ?_
        have hSne : S.Nonempty := (mem_filter.mp hS).2
        refine (card_filter_lt_le _ _ ht (fun _ _ => abs_nonneg _)).trans ?_
        rw [sum_abs_scorr, div_le_div_iff₀ ht hδ]
        have hk : S.card ≤ k := by simpa using card_le_univ S
        have hpow : (H : ℝ) ^ (k - S.card) * (H : ℝ) ^ S.card = (H : ℝ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        calc (H : ℝ) ^ (k - S.card) * (∑ g : Fin S.card → Fin H, |tcorr g X|) * δ
          _ ≤ (H : ℝ) ^ (k - S.card) * (η * (H : ℝ) ^ S.card * X) * δ := by
              gcongr
              exact hX S hSne
          _ = η * (H : ℝ) ^ k * t := by rw [← hpow]; ring
    _ ≤ ∑ _S ∈ (univ : Finset (Finset (Fin k))), η * (H : ℝ) ^ k / δ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = δ * (H : ℝ) ^ k := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, hη]
        push_cast
        field_simp

end

end ChowlaRH

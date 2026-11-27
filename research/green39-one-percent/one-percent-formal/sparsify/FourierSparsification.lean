import FourierDiscrepancy
import SliceConcentration

/-!
# Fourier sparsification for Green 39, Section 5

The empirical character sums are centered at their exact uniform-slice means.
Using exchange constant two and threshold `η * s` in each coordinate gives
total failure probability at most `4 * p * exp (-s * η^2 / 8)`.
-/

open Finset Green39.Concentration
open scoped BigOperators

set_option autoImplicit false

namespace OnePercent.Fourier

noncomputable section

private theorem sliceMean_sum {α : Type*} [DecidableEq α]
    (F : Finset α) {s : ℕ} (hs : 0 < s) (hsF : s ≤ F.card) (w : α → ℝ) :
    sliceMean F s (fun S ↦ ∑ x ∈ S, w x) = (s : ℝ) / F.card * ∑ x ∈ F, w x := by
  classical
  have hcount (x : α) (hx : x ∈ F) :
      ((F.powersetCard s).filter (fun S ↦ x ∈ S)).card =
        (F.card - 1).choose (s - 1) := by
    simpa only [singleton_subset_iff, card_singleton] using
      card_filter_powersetCard_subset ({x} : Finset α) F s (by simpa using hx) hs
  have hsum :
      (∑ S ∈ F.powersetCard s, ∑ x ∈ S, w x) =
        ((F.card - 1).choose (s - 1) : ℝ) * ∑ x ∈ F, w x := by
    calc
      _ = ∑ S ∈ F.powersetCard s, ∑ x ∈ F, if x ∈ S then w x else 0 := by
        apply sum_congr rfl
        intro S hS
        rw [← sum_filter, filter_mem_eq_inter,
          inter_eq_right.mpr (mem_powersetCard.mp hS).1]
      _ = ∑ x ∈ F, ∑ S ∈ F.powersetCard s, if x ∈ S then w x else 0 := sum_comm
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        rw [← sum_filter, sum_const, nsmul_eq_mul, hcount x hx]
  have hchoose : (F.card : ℝ) * ((F.card - 1).choose (s - 1) : ℝ) =
      (s : ℝ) * (F.card.choose s : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm s] using
      (Nat.choose_mul (n := F.card) (k := s) (s := 1) hs).symm)
  have hF : (F.card : ℝ) ≠ 0 := by exact_mod_cast (hs.trans_le hsF).ne'
  have hslice : (F.card.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsF).ne'
  rw [sliceMean, mean, hsum, card_powersetCard]
  field_simp
  linear_combination (∑ x ∈ F, w x) * hchoose

private theorem exchangeLipschitz_sum {α : Type*} [DecidableEq α]
    (F : Finset α) (s : ℕ) {w : α → ℝ} (hw : ∀ x, |w x| ≤ 1) :
    ExchangeLipschitz F s (fun S ↦ ∑ x ∈ S, w x) 2 := by
  intro A hA B hB hAB
  have hBA : (B \ A).card ≤ 1 := by
    have h₁ := card_sdiff_add_card_inter A B
    have h₂ := card_sdiff_add_card_inter B A
    rw [inter_comm B A] at h₂
    have hcard := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
    omega
  have habs (T : Finset α) (hT : T.card ≤ 1) : |∑ x ∈ T, w x| ≤ 1 :=
    (abs_sum_le_sum_abs _ _).trans <| calc
      _ ≤ ∑ _x ∈ T, (1 : ℝ) := sum_le_sum (fun x _ ↦ hw x)
      _ ≤ 1 := by simpa using (show (T.card : ℝ) ≤ 1 by exact_mod_cast hT)
  have hsum (U V : Finset α) :
      (∑ x ∈ U \ V, w x) + (∑ x ∈ U ∩ V, w x) = ∑ x ∈ U, w x := by
    rw [← sum_union (disjoint_sdiff_inter U V), sdiff_union_inter]
  calc
    |(∑ x ∈ A, w x) - ∑ x ∈ B, w x| =
        |(∑ x ∈ A \ B, w x) - ∑ x ∈ B \ A, w x| := by
      rw [← hsum A B, ← hsum B A, inter_comm B A]
      congr 1
      ring
    _ ≤ |∑ x ∈ A \ B, w x| + |∑ x ∈ B \ A, w x| := abs_sub _ _
    _ ≤ 2 := by linarith [habs _ hAB, habs _ hBA]

/-- The finite union bound on a uniform slice, stated for its good event. -/
private theorem one_sub_sum_le_sliceProbability_forall
    {α ι : Type*} [Fintype ι] (F : Finset α) {s : ℕ} (hs : s ≤ F.card)
    (bad : ι → Finset α → Prop) :
    1 - ∑ i, sliceProbability F s (bad i) ≤
      sliceProbability F s (fun S ↦ ∀ i, ¬ bad i S) := by
  classical
  let T := F.powersetCard s
  have ht : 0 < (T.card : ℝ) := by
    exact_mod_cast (by simpa [T, card_powersetCard] using Nat.choose_pos hs : 0 < T.card)
  have hcount : (T.filter (fun S ↦ ¬ ∀ i, ¬ bad i S)).card ≤
      ∑ i, (T.filter (bad i)).card := by
    apply (card_le_card (t := univ.biUnion (fun i : ι ↦ T.filter (bad i))) ?_).trans
      card_biUnion_le
    intro S hS
    obtain ⟨hST, hSbad⟩ := mem_filter.mp hS
    obtain ⟨i, hi⟩ : ∃ i, bad i S := by simpa only [not_forall, not_not] using hSbad
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hST, hi⟩⟩
  have hpartition := T.card_filter_add_card_filter_not (fun S ↦ ∀ i, ¬ bad i S)
  simp only [sliceProbability]
  rw [← sum_div, sub_le_iff_le_add, ← add_div, le_div_iff₀ ht, one_mul, ← Nat.cast_sum,
    ← Nat.cast_add]
  have hgoodFilter :
      @filter _ (fun S ↦ ∀ i, ¬ bad i S) (fun _ ↦ Classical.propDecidable _) T =
        T.filter (fun S ↦ ∀ i, ¬ bad i S) :=
    filter_congr_decidable _ _ _
  rw [hgoodFilter]
  exact Nat.cast_le.mpr (hpartition.ge.trans (Nat.add_le_add_left hcount _))

variable {p : ℕ} [NeZero p]

private def character (a z : ZMod p) : ℂ := ZMod.stdAddChar (-(z * a))

private def coordinate (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

private theorem abs_character_coordinate_le_one (a z : ZMod p) (b : Bool) :
    |coordinate b (character a z)| ≤ 1 := by
  have hn : ‖character a z‖ = 1 := by
    simp [character, AddChar.norm_apply]
  cases b
  · exact (Complex.abs_im_le_norm _).trans_eq hn
  · exact (Complex.abs_re_le_norm _).trans_eq hn

private theorem dft_indicator_eq_sum (F : Finset (ZMod p)) (a : ZMod p) :
    ZMod.dft (indicator F) a = ∑ z ∈ F, character a z := by
  simp [ZMod.dft_apply, smul_eq_mul, indicator, character, mul_ite]

private theorem coordinate_dft_indicator (F : Finset (ZMod p)) (a : ZMod p) (b : Bool) :
    coordinate b (ZMod.dft (indicator F) a) = ∑ z ∈ F, coordinate b (character a z) := by
  rw [dft_indicator_eq_sum]
  cases b <;> simp [coordinate, Complex.re_sum, Complex.im_sum]

private theorem coordinate_sub_real_mul (b : Bool) (z w : ℂ) (r : ℝ) :
    coordinate b (z - (r : ℂ) * w) = coordinate b z - r * coordinate b w := by
  cases b <;> simp [coordinate, Complex.mul_re, Complex.mul_im]

private def observable (i : ZMod p × Bool) (S : Finset (ZMod p)) : ℝ :=
  ∑ z ∈ S, coordinate i.2 (character i.1 z)

private def frequencyBad (F : Finset (ZMod p)) (s : ℕ) (η : ℝ)
    (i : ZMod p × Bool) (S : Finset (ZMod p)) : Prop :=
  η * s ≤ |observable i S - sliceMean F s (observable i)|

/-- Uniform sampling without replacement gives the Fourier residual with at least
`1 - 4 * p * exp (-s * η^2 / 8)` probability. -/
theorem sliceProbability_fourierFit_ge (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {s : ℕ} {η : ℝ} (hs : 0 < s) (hsF : s ≤ F.card) (hη : 0 ≤ η)
    (hfit : FourierFit F μ (5 * η * F.card)) :
    1 - 4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) ≤
      sliceProbability F s (fun S ↦ FourierFit S μ (7 * η * s)) := by
  classical
  let bad := frequencyBad F s η
  have htail (i : ZMod p × Bool) : sliceProbability F s (bad i) ≤
      2 * Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
    have h := sliceProbability_abs_ge_le hsF
      (exchangeLipschitz_sum F s (abs_character_coordinate_le_one i.1 · i.2))
      (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hη (Nat.cast_nonneg s))
    change sliceProbability F s (bad i) ≤ _ at h
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    convert h using 3
    field_simp
    ring
  have hsum : (∑ i, sliceProbability F s (bad i)) ≤
      4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
    calc
      _ ≤ ∑ _i : ZMod p × Bool, 2 * Real.exp (-(s : ℝ) * η ^ 2 / 8) :=
        sum_le_sum (fun i _ ↦ htail i)
      _ = _ := by simp [Fintype.card_prod, ZMod.card, nsmul_eq_mul]; ring
  refine (sub_le_sub_left hsum 1).trans
    ((one_sub_sum_le_sliceProbability_forall F hsF bad).trans ?_)
  unfold sliceProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro S hS
  simp only [mem_filter] at hS ⊢
  obtain ⟨hS, hgood⟩ := hS
  obtain ⟨_, hcard⟩ := mem_powersetCard.mp hS
  refine ⟨hS, fun a ↦ ?_⟩
  let r := (s : ℝ) / F.card
  let d := ZMod.dft (indicator S) a - (r : ℂ) * ZMod.dft (indicator F) a
  have hd (b : Bool) : |coordinate b d| ≤ η * s := by
    have h := lt_of_not_ge (hgood (a, b))
    change |observable (a, b) S - sliceMean F s (observable (a, b))| < η * s at h
    rw [show sliceMean F s (observable (a, b)) =
        r * observable (a, b) F from sliceMean_sum F hs hsF _] at h
    simpa only [d, coordinate_sub_real_mul, coordinate_dft_indicator, observable] using h.le
  have hdNorm : ‖d‖ ≤ 2 * η * s := by
    have hre : |d.re| ≤ η * s := hd true
    have him : |d.im| ≤ η * s := hd false
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hs.trans_le hsF
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hFpos.le
  have hrCard : r * F.card = s := div_mul_cancel₀ _ hFpos.ne'
  have hrCardC : (r : ℂ) * (F.card : ℂ) = s := by exact_mod_cast hrCard
  let m := ZMod.dft (fun z ↦ (μ z : ℂ)) a
  have heq : ZMod.dft (indicator S) a - (S.card : ℂ) * m =
      d + (r : ℂ) * (ZMod.dft (indicator F) a - (F.card : ℂ) * m) := by
    rw [hcard, mul_sub, ← mul_assoc, hrCardC]
    dsimp [d]
    ring
  change ‖ZMod.dft (indicator S) a - (S.card : ℂ) * m‖ ≤ 7 * η * s
  rw [heq]
  calc
    _ ≤ ‖d‖ + ‖(r : ℂ) * (ZMod.dft (indicator F) a - (F.card : ℂ) * m)‖ :=
      norm_add_le _ _
    _ ≤ 2 * η * s + r * (5 * η * F.card) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      exact add_le_add hdNorm (mul_le_mul_of_nonneg_left (hfit a) hr)
    _ = _ := by rw [show r * (5 * η * F.card) = 5 * η * (r * F.card) by ring, hrCard]; ring

/-- Exact finite sufficient criterion for positive success probability. -/
theorem sparsification_tail_lt_one_iff (p s : ℕ) [NeZero p] (η : ℝ) :
    4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) < 1 ↔
      8 * Real.log (4 * (p : ℝ)) < (s : ℝ) * η ^ 2 := by
  have hp := mul_pos (by norm_num : (0 : ℝ) < 4)
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p)) : (0 : ℝ) < p)
  have heq : 4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) =
      Real.exp (Real.log (4 * (p : ℝ)) + -(s : ℝ) * η ^ 2 / 8) := by
    rw [Real.exp_add, Real.exp_log hp]
  rw [heq, ← Real.exp_zero, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Section 5, equation (5). The logarithmic criterion is needed only when
the entire fitted piece cannot be used. -/
theorem exists_fourierFit_sparsify (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (sStar : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hfit : FourierFit F μ (5 * η * F.card))
    (hsize : sStar < F.card → 0 < sStar →
      8 * Real.log (4 * (p : ℝ)) < (sStar : ℝ) * η ^ 2) :
    ∃ S ⊆ F, S.card = min F.card sStar ∧ FourierFit S μ (7 * η * S.card) := by
  classical
  by_cases hF : F.card ≤ sStar
  · refine ⟨F, Subset.rfl, (min_eq_left hF).symm, fun a ↦ (hfit a).trans ?_⟩
    gcongr
    norm_num
  have hlt := lt_of_not_ge hF
  rw [min_eq_right hlt.le]
  by_cases hs : sStar = 0
  · subst sStar
    exact ⟨∅, empty_subset _, card_empty, by simp [FourierFit, dft_indicator_eq_sum]⟩
  have hspos := Nat.pos_of_ne_zero hs
  have ht := (sparsification_tail_lt_one_iff p sStar η).mpr (hsize hlt hspos)
  have hpos := (sub_pos.mpr ht).trans_le
    (sliceProbability_fourierFit_ge F μ hspos hlt.le hη hfit)
  rw [sliceProbability] at hpos
  have hcard := (div_pos_iff_of_pos_right (show (0 : ℝ) < (F.powersetCard sStar).card by
    exact_mod_cast (by simpa [card_powersetCard] using Nat.choose_pos hlt.le :
      0 < (F.powersetCard sStar).card))).mp hpos
  obtain ⟨S, hS⟩ := card_pos.mp (show 0 < ((F.powersetCard sStar).filter
    (fun S ↦ FourierFit S μ (7 * η * sStar))).card by exact_mod_cast hcard)
  obtain ⟨⟨hsub, hsize⟩, hfitS⟩ := (mem_filter.mp hS).imp_left mem_powersetCard.mp
  exact ⟨S, hsub, hsize, hsize.symm ▸ hfitS⟩

/-- The version with the (5η) fit expressed for the uniform probability law on `F`. -/
theorem exists_fourierFit_sparsify_of_uniformLaw (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (sStar : ℕ) {η : ℝ} (hF : F.Nonempty) (hη : 0 ≤ η)
    (hfit : ∀ a : ZMod p,
      ‖ZMod.dft (uniformLaw F) a - ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ 5 * η)
    (hsize : sStar < F.card → 0 < sStar →
      8 * Real.log (4 * (p : ℝ)) < (sStar : ℝ) * η ^ 2) :
    ∃ S ⊆ F, S.card = min F.card sStar ∧ FourierFit S μ (7 * η * S.card) :=
  exists_fourierFit_sparsify F μ sStar hη ((fourierFit_iff_uniformLaw F μ hF _).mpr hfit) hsize

end

end OnePercent.Fourier

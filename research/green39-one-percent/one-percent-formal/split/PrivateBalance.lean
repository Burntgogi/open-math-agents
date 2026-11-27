import SplitLaws
import PrivateIncidence
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The balanced split for the canonical cover (§2)

The cover is selected on the union fiber. On this fiber the nonprivate labels
at any one center form a fixed subset of the population.
-/

open Finset
open scoped BigOperators Classical Pointwise

set_option autoImplicit false

namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Mean of the number of marked points in a uniform slice. -/
theorem sliceMean_card_inter (s D : Finset α) {j : ℕ} (hj : j ≤ s.card) (hD : D ⊆ s) :
    sliceMean s j (fun B ↦ ((B ∩ D).card : ℝ)) = (j : ℝ) / s.card * D.card := by
  classical
  by_cases hj0 : j = 0
  · simp [hj0, sliceMean, mean, powersetCard_zero]
  let S := s.powersetCard j
  have hpoint (x : α) (hx : x ∈ D) :
      sliceProbability s j (fun B ↦ x ∈ B) = (j : ℝ) / s.card := by
    have hE : (fun B : Finset α ↦ x ∈ B) = (fun B ↦ {x} ⊆ B) :=
      funext fun B ↦ propext (by rw [singleton_subset_iff])
    rw [hE, sliceProbability_contains s {x} j (singleton_subset_iff.mpr (hD hx))
      (by simpa only [card_singleton] using (show 1 ≤ j by omega)), card_singleton]
    have hs : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr ⟨x, hD hx⟩
    have hc : (0 : ℝ) < s.card.choose j := by exact_mod_cast Nat.choose_pos hj
    have h := Nat.choose_mul (n := s.card) (k := j) (s := 1) (Nat.pos_of_ne_zero hj0)
    simp only [Nat.choose_one_right] at h
    have h' : (s.card.choose j : ℝ) * j = (s.card : ℝ) * (s.card - 1).choose (j - 1) := by
      exact_mod_cast h
    apply (div_eq_div_iff hc.ne' hs.ne').mpr
    linarith only [h']
  have hcount (B : Finset α) : ((B ∩ D).card : ℝ) = ∑ x ∈ D, if x ∈ B then 1 else 0 := by
    rw [← sum_filter]
    have h : (D.filter fun x ↦ x ∈ B) = B ∩ D := by
      ext x
      simp [and_comm]
    rw [h]
    simp
  have hin (x : α) :
      (∑ B ∈ S, if x ∈ B then (1 : ℝ) else 0) / S.card =
        sliceProbability s j (fun B ↦ x ∈ B) := by
    rw [← sum_filter]
    unfold sliceProbability
    simp only [sum_const, nsmul_eq_mul, mul_one]
    congr 2
    apply congrArg Finset.card
    ext B
    simp only [mem_filter, S]
  change (∑ B ∈ S, ((B ∩ D).card : ℝ)) / S.card = _
  rw [sum_congr rfl (fun B _ ↦ hcount B), sum_comm, sum_div]
  calc
    _ = ∑ x ∈ D, sliceProbability s j (fun B ↦ x ∈ B) :=
      sum_congr rfl (fun x _ ↦ hin x)
    _ = ∑ _x ∈ D, (j : ℝ) / s.card := sum_congr rfl hpoint
    _ = _ := by simp [mul_comm]

/-- Exchanging one point changes the number of marked points by at most one. -/
theorem exchangeLipschitz_card_inter (s D : Finset α) (j : ℕ) :
    ExchangeLipschitz s j (fun B ↦ ((B ∩ D).card : ℝ)) 1 := by
  intro B hB C hC hd
  have hswap : (C \ B).card ≤ 1 :=
    (card_sdiff_comm ((mem_powersetCard.mp hC).2.trans (mem_powersetCard.mp hB).2.symm)).le.trans hd
  have hstep (U V : Finset α) (hUV : (U \ V).card ≤ 1) :
      ((U ∩ D).card : ℝ) ≤ (V ∩ D).card + 1 := by
    have hsub : (U ∩ D) \ (V ∩ D) ⊆ U \ V := by
      intro x hx
      simp only [mem_sdiff, mem_inter] at hx ⊢
      tauto
    have hdiff := (card_le_card hsub).trans hUV
    have hinter : ((U ∩ D) ∩ (V ∩ D)).card ≤ (V ∩ D).card := card_le_card inter_subset_right
    have hadd := card_sdiff_add_card_inter (U ∩ D) (V ∩ D)
    exact_mod_cast (show (U ∩ D).card ≤ (V ∩ D).card + 1 by omega)
  exact abs_le.mpr ⟨by linarith only [hstep C B hswap], by linarith only [hstep B C hd]⟩

variable {p : ℕ}

/-- All covers eligible for the one-percent cover budget. -/
def smallCovers [NeZero p] (A : Finset (ZMod p)) : Finset (Finset (ZMod p)) :=
  (univ : Finset (ZMod p)).powerset.filter fun T ↦
    A + T = univ ∧ (T.card : ℝ) ≤ 1.01 * p / A.card

/-- Compare covers lexicographically by their sorted lists of representatives. -/
def coverKey (T : Finset (ZMod p)) : List ℕ :=
  (T.image ZMod.val).sort

theorem coverKey_injective [NeZero p] : Function.Injective (coverKey (p := p)) := by
  intro T U h
  have hi : T.image ZMod.val = U.image ZMod.val := by
    simpa only [coverKey, sort_toFinset] using congrArg List.toFinset h
  ext t
  exact ⟨fun ht ↦ by
    obtain ⟨u, hu, hval⟩ := mem_image.mp (hi ▸ mem_image_of_mem ZMod.val ht)
    rwa [ZMod.val_injective p hval] at hu, fun hu ↦ by
    obtain ⟨v, hv, hval⟩ := mem_image.mp (hi.symm ▸ mem_image_of_mem ZMod.val hu)
    rwa [ZMod.val_injective p hval] at hv⟩

/-- The first eligible cover in lexicographic order, and the empty set when none exists. -/
def canonicalCover [NeZero p] (A : Finset (ZMod p)) : Finset (ZMod p) :=
  if h : (smallCovers A).Nonempty then (exists_min_image (smallCovers A) coverKey h).choose
  else ∅

theorem canonicalCover_spec [NeZero p] {A : Finset (ZMod p)} (h : (smallCovers A).Nonempty) :
    canonicalCover A ∈ smallCovers A ∧
      ∀ T ∈ smallCovers A, coverKey (canonicalCover A) ≤ coverKey T := by
  unfold canonicalCover
  rw [dif_pos h]
  exact (exists_min_image (smallCovers A) coverKey h).choose_spec

theorem canonicalCover_nearPrivate_card [NeZero p] {A : Finset (ZMod p)}
    (hcover : (smallCovers A).Nonempty) (hk : 0 < A.card) (hsquare : A.card ^ 2 ≤ p) :
    (A.card : ℝ) / 9 ≤ (nearPrivateCenters A (canonicalCover A) (0.0225 * A.card)).card := by
  obtain ⟨hcov, hbudget⟩ := (mem_filter.mp (canonicalCover_spec hcover).1).2
  obtain ⟨h₁, h₂, h₃⟩ := card_nearPrivateCenters_onePercent hcov hk hsquare hbudget
  exact h₃.trans (h₂.trans h₁)

/-- Failure is a strict exceedance at a near-private center in either half. -/
def BalanceFailure (A T A₁ A₂ : Finset (ZMod p)) : Prop :=
  ∃ t ∈ nearPrivateCenters A T (0.0225 * A.card),
    (0.0114 : ℝ) * A.card < (nonprivateLabels A T A₁ t).card ∨
    (0.0114 : ℝ) * A.card < (nonprivateLabels A T A₂ t).card

/-- On a balanced split, any two sets of near-private centers satisfy both bounds in (3). -/
theorem balanced_halves_bounds_of_nearPrivate {A T A₁ A₂ R S : Finset (ZMod p)}
    (hsplit : A₁ ∪ A₂ = A) (hdisjoint : Disjoint A₁ A₂) (hhalf : A₁.card = A.card / 2)
    (hR : R ⊆ nearPrivateCenters A T (0.0225 * A.card))
    (hS : S ⊆ nearPrivateCenters A T (0.0225 * A.card))
    (hbalanced : ¬ BalanceFailure A T A₁ A₂) :
    let U := A₁ + R
    (((A.card / 2 : ℕ) : ℝ) - 0.0114 * A.card) * R.card ≤ U.card ∧
      ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
        0.0114 * (A.card : ℝ) * S.card := by
  apply Green39.balanced_halves_bounds hsplit hdisjoint hhalf
    (fun _ ht ↦ (mem_nearPrivateCenters.mp (hR ht)).1)
    (fun _ ht ↦ (mem_nearPrivateCenters.mp (hS ht)).1)
  · exact fun t ht ↦ le_of_not_gt (fun h ↦ hbalanced ⟨t, hR ht, Or.inl h⟩)
  · exact fun t ht ↦ le_of_not_gt (fun h ↦ hbalanced ⟨t, hS ht, Or.inr h⟩)

private theorem nonprivateLabels_eq_inter {A T B : Finset (ZMod p)} (hB : B ⊆ A) (t : ZMod p) :
    nonprivateLabels A T B t = B ∩ nonprivateLabels A T A t := by
  ext a
  simp only [mem_nonprivateLabels, mem_inter]
  exact ⟨fun ⟨ha, h⟩ ↦ ⟨ha, hB ha, h⟩, fun ⟨ha, _, h⟩ ↦ ⟨ha, h⟩⟩

private theorem sliceProbability_center_failure (A T : Finset (ZMod p)) (t : ZMod p)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ A.card) (hjhalf : 2 * j ≤ A.card + 1) (hk : 225 ≤ A.card)
    (ht : t ∈ nearPrivateCenters A T (0.0225 * A.card)) :
    sliceProbability A j
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card) ≤
      Real.exp (-(A.card : ℝ) / 200000000) := by
  let D := nonprivateLabels A T A t
  have hD : D ⊆ A := fun _ hx ↦ (mem_nonprivateLabels.mp hx).1
  have hsmall : (D.card : ℝ) ≤ 0.0225 * A.card := (mem_nearPrivateCenters.mp ht).2
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  let f : Finset (ZMod p) → ℝ := fun B ↦ (B ∩ D).card
  have hjhalf' : 2 * (j : ℝ) ≤ (A.card : ℝ) + 1 := by exact_mod_cast hjhalf
  have hμ : sliceMean A j f ≤ 0.01125 * ((A.card : ℝ) + 1) := by
    rw [sliceMean_card_inter A D hj hD]
    calc
      _ ≤ ((j : ℝ) / A.card) * (0.0225 * A.card) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 0.0225 * j := by field_simp
      _ ≤ _ := by linarith only [hjhalf']
  have hk' : (225 : ℝ) ≤ A.card := by exact_mod_cast hk
  let u : ℝ := (A.card : ℝ) / 10000
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hevent : sliceProbability A j
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card) ≤
      sliceProbability A j (fun B ↦ u ≤ f B - sliceMean A j f) := by
    simp only [sliceProbability_eq_probability]
    apply probability_mono
    intro B hB h
    rw [nonprivateLabels_eq_inter (mem_powersetCard.mp hB).1] at h
    change (0.0114 : ℝ) * A.card < f B at h
    dsimp [u]
    linarith only [h, hμ, hk']
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
  have hj' : (j : ℝ) ≤ A.card := by exact_mod_cast hj
  refine hevent.trans ((sliceProbability_ge_le hj (exchangeLipschitz_card_inter A D j)
    zero_le_one hu).trans (Real.exp_le_exp.mpr ?_))
  rw [one_pow, mul_one]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (j : ℝ))).mpr
  dsimp [u]
  have hm := mul_le_mul_of_nonneg_left hj' hpos.le
  nlinarith only [hm]

/-- Simultaneous balance at all near-private centers, given the full set and cover. -/
theorem sliceProbability_balance_failure [NeZero p] (A T : Finset (ZMod p)) {k₁ k₂ : ℕ}
    (hA : A.card = k₁ + k₂) (hhalf : k₁ = A.card / 2) (hk : 225 ≤ A.card) :
    sliceProbability A k₁ (fun B ↦ BalanceFailure A T B (A \ B)) ≤
      2 * p * Real.exp (-(A.card : ℝ) / 200000000) := by
  let good := nearPrivateCenters A T (0.0225 * A.card)
  let index := good ×ˢ (univ : Finset Bool)
  let E (w : ZMod p × Bool) (B : Finset (ZMod p)) : Prop :=
    (0.0114 : ℝ) * A.card <
      (nonprivateLabels A T (if w.2 then A \ B else B) w.1).card
  have hE : (fun B ↦ BalanceFailure A T B (A \ B)) = (fun B ↦ ∃ w ∈ index, E w B) := by
    funext B
    apply propext
    constructor
    · rintro ⟨t, ht, h₁ | h₂⟩
      · exact ⟨(t, false), mem_product.mpr ⟨ht, mem_univ _⟩, h₁⟩
      · exact ⟨(t, true), mem_product.mpr ⟨ht, mem_univ _⟩, h₂⟩
    · rintro ⟨⟨t, b⟩, hw, h⟩
      refine ⟨t, (mem_product.mp hw).1, ?_⟩
      cases b
      · exact Or.inl h
      · exact Or.inr h
  have htail (w : ZMod p × Bool) (hw : w ∈ index) :
      sliceProbability A k₁ (E w) ≤ Real.exp (-(A.card : ℝ) / 200000000) := by
    have ht := (mem_product.mp hw).1
    obtain ⟨t, b⟩ := w
    cases b
    · exact sliceProbability_center_failure A T t (by omega) (by omega) (by omega) hk ht
    · change sliceProbability A k₁
          (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T (A \ B) t).card) ≤ _
      rw [sliceProbability_complement A k₁ k₂ hA
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card)]
      exact sliceProbability_center_failure A T t (by omega) (by omega) (by omega) hk ht
  rw [hE]
  calc
    _ ≤ ∑ w ∈ index, sliceProbability A k₁ (E w) := by
      simp only [sliceProbability_eq_probability]
      exact probability_exists_le_sum _ _ _
    _ ≤ ∑ _w ∈ index, Real.exp (-(A.card : ℝ) / 200000000) := sum_le_sum htail
    _ = ((good.card : ℝ) * 2) * Real.exp (-(A.card : ℝ) / 200000000) := by
      simp [index, card_product]
    _ ≤ _ := by
      have hcard : (good.card : ℝ) ≤ p := by
        exact_mod_cast (show good.card ≤ p from by simpa [ZMod.card] using card_le_univ good)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith only [hcard]

/-- The joint event of cover existence and a failed balance for the canonical cover. -/
def CanonicalBalanceFailure [NeZero p] (q : Finset (ZMod p) × Finset (ZMod p)) : Prop :=
  let A := q.1 ∪ q.2
  (smallCovers A).Nonempty ∧ BalanceFailure A (canonicalCover A) q.1 q.2

/-- Averaging over the full set preserves the simultaneous bound. -/
theorem canonical_balance_failure_bound [NeZero p] {k : ℕ} (hk : 225 ≤ k) :
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
        CanonicalBalanceFailure ≤ 2 * p * Real.exp (-(k : ℝ) / 200000000) := by
  rw [probability_eq_mean_union]
  apply mean_le_of_forall_le (by positivity)
  intro A hA
  have hsize : A.card = k / 2 + (k - k / 2) := (mem_powersetCard.mp hA).2
  have hcard : A.card = k := by omega
  have htail := sliceProbability_balance_failure A (canonicalCover A) hsize (by omega) (by omega)
  rw [hcard] at htail
  refine le_trans ?_ htail
  simp only [sliceProbability_eq_probability]
  apply probability_mono
  intro B hB
  unfold CanonicalBalanceFailure
  rw [show B ∪ (A \ B) = A from sup_sdiff_cancel_right (mem_powersetCard.mp hB).1]
  exact And.right

open Filter
open scoped Topology

/-- Joint failure probability in the actual square-root-sized split model. -/
def canonicalBalanceFailureProbability (p : ℕ) : ℝ :=
  if hp : p = 0 then 0
  else
    letI : NeZero p := ⟨hp⟩
    let k := p.sqrt
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
      CanonicalBalanceFailure

/-- The joint failure probability tends to zero even along all positive moduli. -/
theorem tendsto_canonical_balance_failure :
    Tendsto canonicalBalanceFailureProbability atTop (𝓝 0) := by
  let C : ℝ := 200000000
  let y (p : ℕ) : ℝ := (p.sqrt : ℝ) / C
  have hroot : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop.mpr fun k ↦ (eventually_ge_atTop (k ^ 2)).mono ?_
    exact fun _ hp ↦ Nat.le_sqrt'.mpr hp
  have hy : Tendsto y atTop atTop :=
    Tendsto.atTop_div_const (by positivity) (tendsto_natCast_atTop_atTop.comp hroot)
  have hf : Tendsto (fun p : ℕ ↦ y p ^ (2 : ℕ) * Real.exp (-y p)) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hy
  have hc : Tendsto (fun _ : ℕ ↦ 8 * C ^ (2 : ℕ)) atTop (𝓝 (8 * C ^ (2 : ℕ))) :=
    tendsto_const_nhds
  have ht : Tendsto (fun p ↦ (8 * C ^ (2 : ℕ)) * (y p ^ (2 : ℕ) * Real.exp (-y p)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.mul hf
  refine squeeze_zero' (Eventually.of_forall ?_) ?_ ht
  · intro p
    unfold canonicalBalanceFailureProbability
    split
    · rfl
    · unfold probability
      positivity
  · filter_upwards [eventually_ge_atTop (225 ^ 2 : ℕ)] with p hp
    have hk : 225 ≤ p.sqrt := Nat.le_sqrt'.mpr hp
    have hp0 : p ≠ 0 := by omega
    let _ : NeZero p := ⟨hp0⟩
    rw [canonicalBalanceFailureProbability, dif_neg hp0]
    refine (canonical_balance_failure_bound hk).trans ?_
    have hp' : (p : ℝ) ≤ ((p.sqrt : ℝ) + 1) ^ 2 := by
      exact_mod_cast (Nat.lt_succ_sqrt' p).le
    have hroot' : (1 : ℝ) ≤ p.sqrt := by exact_mod_cast (show 1 ≤ p.sqrt by omega)
    have hcoeff : (2 : ℝ) * p ≤ 8 * (p.sqrt : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ (p.sqrt : ℝ) + 1 by positivity)
        (show (p.sqrt : ℝ) + 1 ≤ 2 * p.sqrt by linarith only [hroot']) 2
      nlinarith only [hp', hsq]
    calc
      _ ≤ (8 * (p.sqrt : ℝ) ^ 2) * Real.exp (-(p.sqrt : ℝ) / 200000000) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
      _ = _ := by
        unfold y C
        rw [neg_div]
        ring

end

end Green39.Split

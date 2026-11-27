import SliceRegularity

/-!
# Finite probability estimate for terminal containers

On the uniform slice, the complement of the joint event is bounded by the
irregularity probability plus one lower tail for the uncovered set and a
union of upper tails for the scores. The cover conclusion is deterministic
on that joint event.
-/

open Finset
open scoped BigOperators Classical Pointwise

namespace Green39.Terminal

open Concentration

noncomputable section

variable {p k : ℕ} [NeZero p]

/-- Avoidance probability of a fixed set of size «m» on the uniform slice. -/
def rho (p k m : ℕ) : ℝ := ((p - m).choose k : ℝ) / (p.choose k : ℝ)

/-- The exact mean of an outside score, when «0 < k». -/
def scoreMean (p k m : ℕ) : ℝ :=
  (p : ℝ) * ((p - 1 - m).choose (k - 1) : ℝ) / (p.choose k : ℝ)

theorem rho_nonneg (p k m : ℕ) : 0 ≤ rho p k m := by
  unfold rho
  positivity

theorem rho_pos {p k m : ℕ} (hk : k ≤ p - m) : 0 < rho p k m := by
  unfold rho
  have := Nat.choose_pos hk
  have := Nat.choose_pos (hk.trans (Nat.sub_le p m))
  positivity

theorem mean_holes (P : Finset (ZMod p)) :
    sliceMean univ k (fun A ↦ ((uncovered A P).card : ℝ)) = (p : ℝ) * rho p k P.card := by
  simp only [sliceMean, mean, card_powersetCard, card_univ, ZMod.card, ← Nat.cast_sum,
    sum_card_uncovered, Nat.cast_mul, rho, mul_div_assoc]

theorem mean_score (P : Finset (ZMod p)) {t : ZMod p} (ht : t ∉ P) (hk : 0 < k) :
    sliceMean univ k (fun A ↦ ((outsideHits A P t).card : ℝ)) = scoreMean p k P.card := by
  simp only [sliceMean, mean, card_powersetCard, card_univ, ZMod.card, ← Nat.cast_sum,
    sum_card_outsideHits P ht hk, Nat.cast_mul, scoreMean]

theorem scoreMean_eq {p k m : ℕ} (hk : 0 < k) (hm : m < p) :
    scoreMean p k m = (k : ℝ) * rho p k m * ((p : ℝ) / ((p : ℝ) - m)) := by
  have hnat : (p - m) * (p - 1 - m).choose (k - 1) = (p - m).choose k * k := by
    have h := Nat.add_one_mul_choose_eq (p - 1 - m) (k - 1)
    rwa [show p - 1 - m + 1 = p - m by omega, show k - 1 + 1 = k by omega] at h
  have hreal : ((p : ℝ) - m) * ((p - 1 - m).choose (k - 1) : ℝ) =
      ((p - m).choose k : ℝ) * k := by
    rw [← Nat.cast_sub hm.le]
    exact_mod_cast hnat
  have hpm : (p : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm.ne')
  have hfactor : ((p - 1 - m).choose (k - 1) : ℝ) =
      ((p - m).choose k : ℝ) * k / ((p : ℝ) - m) := by
    apply (eq_div_iff hpm).mpr
    rwa [mul_comm]
  rw [scoreMean, rho, hfactor]
  ring

private theorem card_lost_holes_le (A B P : Finset (ZMod p)) :
    (uncovered A P \ uncovered B P).card ≤ P.card * (B \ A).card := by
  let additions := (B \ A).biUnion (fun v ↦ ({v} : Finset (ZMod p)) + P)
  have hsub : uncovered A P \ uncovered B P ⊆ additions := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := mem_sdiff.mp hx
    have hxBP : x ∈ B + P := by
      by_contra h
      exact hxB (mem_sdiff.mpr ⟨mem_univ _, h⟩)
    obtain ⟨v, hvB, a, ha, he⟩ := mem_add.mp hxBP
    have hvA : v ∉ A := fun hvA ↦ (mem_sdiff.mp hxA).2 (mem_add.mpr ⟨v, hvA, a, ha, he⟩)
    exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hvB, hvA⟩,
      mem_add.mpr ⟨v, mem_singleton_self _, a, ha, he⟩⟩
  calc
    _ ≤ additions.card := card_le_card hsub
    _ ≤ ∑ v ∈ B \ A, (({v} : Finset (ZMod p)) + P).card := card_biUnion_le
    _ = _ := by simp [card_singleton_add, mul_comm]

theorem holes_exchangeLipschitz (P : Finset (ZMod p)) :
    ExchangeLipschitz univ k (fun A ↦ ((uncovered A P).card : ℝ))
      (max 1 (P.card : ℝ)) := by
  intro A hA B hB hAB
  have hsize : A.card = B.card := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
  have hBA : (B \ A).card ≤ 1 := card_sdiff_comm hsize ▸ hAB
  have hd (U V : Finset (ZMod p)) (h : (V \ U).card ≤ 1) :
      ((uncovered U P).card : ℝ) - (uncovered V P).card ≤ (P.card : ℝ) := by
    have hle := (le_card_sdiff (uncovered V P) (uncovered U P)).trans (card_lost_holes_le U V P)
    have hcard : (uncovered U P).card ≤ (uncovered V P).card + P.card := by
      have hh := Nat.mul_le_mul_left P.card h
      omega
    have hr : ((uncovered U P).card : ℝ) ≤ (uncovered V P).card + (P.card : ℝ) := by
      exact_mod_cast hcard
    linarith
  exact abs_sub_le_iff.mpr ⟨(hd A B hBA).trans (le_max_right _ _),
    (hd B A hAB).trans (le_max_right _ _)⟩

private theorem score_le_of_mem {A : Finset (ZMod p)} (hA : A ∈ (univ : Finset (ZMod p)).powersetCard k)
    (P : Finset (ZMod p)) (t : ZMod p) : ((outsideHits A P t).card : ℝ) ≤ (k : ℝ) := by
  have h := card_le_card (inter_subset_left :
    outsideHits A P t ⊆ A + {t})
  rw [card_add_singleton, (mem_powersetCard.mp hA).2] at h
  exact_mod_cast h

private theorem score_zero_of_mem (A P : Finset (ZMod p)) {t : ZMod p} (ht : t ∈ P) :
    (outsideHits A P t).card = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hadd, hxH⟩ := mem_inter.mp hx
  obtain ⟨a, ha, v, hv, he⟩ := mem_add.mp hadd
  exact (mem_sdiff.mp hxH).2 (mem_add.mpr ⟨a, ha, v, (mem_singleton.mp hv).symm ▸ ht, he⟩)

private theorem score_regular_lipschitz (P : Finset (ZMod p)) (L : ℕ) (t : ZMod p)
    {A B : Finset (ZMod p)} (hsize : A.card = B.card)
    (hA : OutsideRegular A P L) (hB : OutsideRegular B P L) :
    |((outsideHits A P t).card : ℝ) - (outsideHits B P t).card| ≤
      (1 + (L : ℝ)) * ((A \ B).card : ℝ) := by
  have hh := dist_card_outsideHits_le hsize hA hB t
  have he : ((Nat.dist (outsideHits A P t).card (outsideHits B P t).card : ℕ) : ℝ) =
      |((outsideHits A P t).card : ℝ) - (outsideHits B P t).card| := by
    rcases le_total (outsideHits A P t).card (outsideHits B P t).card with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
      ring
    · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
  rw [← he]
  exact_mod_cast hh

/-- The tail bound consists of one regularity union bound, a lower tail for
the holes, and at most «p» upper tails with deviation «u». -/
def failureBound (p k m L : ℕ) (δ u : ℝ) : ℝ :=
  irregularBound p k m L +
    Real.exp (-(δ * (p : ℝ) * rho p k m) ^ 2 / (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) +
    (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2))

/-- The good event includes regularity, the lower bound on holes and the cap on every score. -/
def JointGood (P : Finset (ZMod p)) (k L : ℕ) (δ : ℝ) (A : Finset (ZMod p)) : Prop :=
  OutsideRegular A P L ∧
  (1 - δ) * (p : ℝ) * rho p k P.card ≤ (uncovered A P).card ∧
  ∀ t : ZMod p, ((outsideHits A P t).card : ℝ) ≤ (1 + δ) * k * rho p k P.card

/-- Finite simultaneous estimate on the true uniform slice. The margin condition
pays for the shift between the genuine score and the clipped extension. -/
theorem probability_not_jointGood_le (P : Finset (ZMod p)) (L : ℕ) {δ u : ℝ}
    (hk : 0 < k) (hkp : k ≤ p) (hδ : 0 ≤ δ) (hu : 0 ≤ u)
    (hmargin : scoreMean p k P.card + (k : ℝ) * irregularBound p k P.card L + u ≤
      (1 + δ) * k * rho p k P.card) :
    probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤ failureBound p k P.card L δ u := by
  let s : Finset (ZMod p) := univ
  let m := P.card
  let r := rho p k m
  let Q := irregularBound p k m L
  let reg (A : Finset (ZMod p)) := OutsideRegular A P L
  let D := (s.powersetCard k).filter reg
  have hs : k ≤ s.card := by simpa [s, ZMod.card] using hkp
  have hQ : probability p k (fun A ↦ ¬ reg A) ≤ Q := probability_irregular_le P L
  by_cases hQ1 : Q < 1
  swap
  · have hprob : probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤ 1 := by
      linarith [sliceProbability_add_compl s hs (fun A ↦ ¬ JointGood P k L δ A),
        sliceProbability_nonneg s k (fun A ↦ ¬ ¬ JointGood P k L δ A)]
    refine hprob.trans ?_
    unfold failureBound
    have hQ' : 1 ≤ irregularBound p k P.card L := le_of_not_gt hQ1
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    linarith [Real.exp_nonneg (-(δ * (p : ℝ) * rho p k P.card) ^ 2 /
      (2 * (k : ℝ) * (max 1 (P.card : ℝ)) ^ 2)),
      mul_nonneg hp0 (Real.exp_nonneg (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)))]
  have hD : D.Nonempty := by
    by_contra h
    have hD0 : D = ∅ := not_nonempty_iff_eq_empty.mp h
    have hreg0 : probability p k reg = 0 := by
      change (D.card : ℝ) / (s.powersetCard k).card = 0
      rw [hD0, card_empty, Nat.cast_zero, zero_div]
    have hc := sliceProbability_add_compl s hs reg
    change probability p k reg + probability p k (fun A ↦ ¬ reg A) = 1 at hc
    linarith
  let X (t : ZMod p) (A : Finset (ZMod p)) : ℝ := (outsideHits A P t).card
  let F (t : ZMod p) := regularExtension D hD (X t) (1 + (L : ℝ)) k
  have hF_eq (t : ZMod p) {A : Finset (ZMod p)} (hA : A ∈ s.powersetCard k)
      (hreg : reg A) : F t A = X t A := by
    apply regularExtension_eq hD ?_ (mem_filter.mpr ⟨hA, hreg⟩) (score_le_of_mem hA P t)
    intro B hB C hC
    have hb := mem_filter.mp hB
    have hc := mem_filter.mp hC
    exact score_regular_lipschitz P L t
      ((mem_powersetCard.mp hb.1).2.trans (mem_powersetCard.mp hc.1).2.symm) hb.2 hc.2
  have hFmean (t : ZMod p) (ht : t ∉ P) :
      sliceMean s k (F t) ≤ scoreMean p k m + (k : ℝ) * Q := by
    have hdev := sliceMean_sub_abs_le (s := s) (k := k) (E := reg) (K := (k : ℝ))
      (f := F t) (g := X t) (fun A hA ↦ ?_) (fun A hA hr ↦ hF_eq t hA hr)
    · have hm : sliceMean s k (X t) = scoreMean p k m := mean_score P ht hk
      have h := (le_abs_self _).trans hdev
      rw [hm] at h
      have hmul := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg k : 0 ≤ (k : ℝ))
      change _ ≤ (k : ℝ) * probability p k (fun A ↦ ¬ reg A) at h
      linarith
    · apply abs_sub_le_iff.mpr
      have hF0 : 0 ≤ F t A := regularExtension_nonneg hD (fun _ _ ↦ by dsimp [X]; positivity)
        (by positivity) (Nat.cast_nonneg _) _
      have hF1 : F t A ≤ (k : ℝ) := regularExtension_le hD _ _ _ _
      have hX0 : 0 ≤ X t A := Nat.cast_nonneg _
      have hX1 : X t A ≤ (k : ℝ) := score_le_of_mem hA P t
      constructor <;> linarith
  let H (A : Finset (ZMod p)) : ℝ := (uncovered A P).card
  let lower (A : Finset (ZMod p)) := δ * (p : ℝ) * r ≤ sliceMean s k H - H A
  let upper (t : ZMod p) (A : Finset (ZMod p)) := u ≤ F t A - sliceMean s k (F t)
  have hsub : probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤
      probability p k (fun A ↦ ¬ reg A ∨ lower A ∨ ∃ t ∈ (univ \ P), upper t A) := by
    apply sliceProbability_mono
    intro A hA hbad
    by_cases hreg : reg A
    swap
    · exact Or.inl hreg
    right
    by_cases hH : (1 - δ) * (p : ℝ) * r ≤ H A
    swap
    · left
      dsimp only [lower]
      have hmean : sliceMean s k H = (p : ℝ) * r := mean_holes P
      rw [hmean]
      linarith
    right
    have hnot : ¬ ∀ t : ZMod p, X t A ≤ (1 + δ) * (k : ℝ) * r :=
      fun h ↦ hbad ⟨hreg, hH, h⟩
    obtain ⟨t, ht⟩ := not_forall.mp hnot
    have htP : t ∉ P := by
      intro hm
      apply ht
      dsimp only [X]
      rw [score_zero_of_mem A P hm, Nat.cast_zero]
      exact mul_nonneg (by positivity) (rho_nonneg _ _ _)
    refine ⟨t, mem_sdiff.mpr ⟨mem_univ _, htP⟩, ?_⟩
    dsimp only [upper]
    rw [hF_eq t hA hreg]
    have hF := hFmean t htP
    change scoreMean p k m + (k : ℝ) * Q + u ≤ (1 + δ) * (k : ℝ) * r at hmargin
    linarith [lt_of_not_ge ht]
  have hlower : probability p k lower ≤
      Real.exp (-(δ * (p : ℝ) * r) ^ 2 / (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) :=
    sliceProbability_le_le hs (holes_exchangeLipschitz (k := k) P)
      (le_trans zero_le_one (le_max_left _ _))
      (mul_nonneg (mul_nonneg hδ (Nat.cast_nonneg _)) (rho_nonneg p k m))
  have hUpper (t : ZMod p) :
      probability p k (upper t) ≤
        Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) :=
    sliceProbability_ge_le hs
      (regularExtension_exchangeLipschitz hD (X t) (show 0 ≤ 1 + (L : ℝ) by positivity) k s k)
      (by positivity) hu
  refine hsub.trans ((sliceProbability_or_le s k _ _).trans ?_)
  refine (add_le_add hQ (sliceProbability_or_le s k _ _)).trans ?_
  refine (add_le_add (le_refl Q) (add_le_add hlower (sliceProbability_exists_le s k _ _))).trans ?_
  have hsum : ∑ t ∈ (univ \ P), probability p k (upper t) ≤
      (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) := by
    calc
      _ ≤ ∑ _t ∈ (univ \ P), Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) :=
        sum_le_sum fun t _ ↦ hUpper t
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact_mod_cast ((card_le_card (sdiff_subset (s := (univ : Finset (ZMod p))) (t := P))).trans_eq
          (by rw [card_univ, ZMod.card]))
  refine (add_le_add (le_refl Q) (add_le_add (le_refl _) hsum)).trans_eq ?_
  dsimp [failureBound, Q, r, m]
  ring

/-- Every cover has the stated number of centers outside each listed container. -/
def CoversOutside (P : Finset (ZMod p)) (k : ℕ) (ζ : ℝ) (A : Finset (ZMod p)) : Prop :=
  ∀ T : Finset (ZMod p), A + T = univ →
    (1 - ζ) * (p : ℝ) / k ≤ ((T \ P).card : ℝ)

theorem coversOutside_of_jointGood {P : Finset (ZMod p)} {L : ℕ} {δ ζ : ℝ}
    {A : Finset (ZMod p)} (hk : 0 < k) (hδ : 0 ≤ δ) (hρ : 0 < rho p k P.card)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ)) (hA : JointGood P k L δ A) :
    CoversOutside P k ζ A := by
  intro T hT
  calc
    _ ≤ (1 - δ) / (1 + δ) * (p : ℝ) / k := by
      gcongr
    _ ≤ _ := by
      have hh : (1 - δ) * (Fintype.card (ZMod p) : ℝ) * rho p k P.card ≤
          (uncovered A P).card := by simpa only [ZMod.card] using hA.2.1
      simpa only [ZMod.card] using le_card_outside_of_bounds A P T hT hk hδ hρ hh
        (fun t _ ↦ hA.2.2 t)

/-- Finite version of (1) for a deterministic list, with a separate bound for
each container. -/
theorem probability_not_coversOutside_list_le (Ps : Finset (Finset (ZMod p)))
    (L : ℕ) {δ ζ u : ℝ}
    (hk : 0 < k) (hkp : k ≤ p) (hδ : 0 ≤ δ) (hu : 0 ≤ u)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ))
    (hρ : ∀ P ∈ Ps, 0 < rho p k P.card)
    (hmargin : ∀ P ∈ Ps, scoreMean p k P.card + (k : ℝ) * irregularBound p k P.card L + u ≤
      (1 + δ) * k * rho p k P.card) :
    probability p k (fun A ↦ ¬ ∀ P ∈ Ps, CoversOutside P k ζ A) ≤
      ∑ P ∈ Ps, failureBound p k P.card L δ u := by
  refine (sliceProbability_mono (F := fun A ↦ ∃ P ∈ Ps, ¬ JointGood P k L δ A) ?_).trans
    ((sliceProbability_exists_le _ _ _ _).trans ?_)
  · intro A _ hA
    by_contra h
    apply hA
    exact fun P hP ↦ coversOutside_of_jointGood hk hδ (hρ P hP) hζ
      (by_contra fun hj ↦ h ⟨P, hP, hj⟩)
  · exact sum_le_sum fun P hP ↦ probability_not_jointGood_le P L hk hkp hδ hu (hmargin P hP)

end

end Green39.Terminal


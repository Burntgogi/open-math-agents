import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Finite outside restriction for Green's problem 39

The sample space is `Finset.univ.powersetCard k`, as in
`Green39.proportionCoverable`. The counts below are the numerators of
the two uniform expectations in §1 of `overnight-astra/review/one-percent.md`.
The counting identities apply to every nonzero modulus. When `k > p`,
the sums and the binomial counts vanish.
-/

open scoped Pointwise
open Finset

namespace Green39

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The points left uncovered by the centers in `P`. -/
def uncovered (A P : Finset G) : Finset G := univ \ (A + P)

/-- The points of the translate by `t` that the centers in `P` leave uncovered. -/
def outsideHits (A P : Finset G) (t : G) : Finset G := (A + {t}) ∩ uncovered A P

private def allowed (P : Finset G) (x : G) : Finset G :=
  univ \ P.image (fun v ↦ x - v)

private theorem mem_uncovered_iff_subset_allowed {A P : Finset G} {x : G} :
    x ∈ uncovered A P ↔ A ⊆ allowed P x := by
  simp only [uncovered, mem_sdiff, mem_univ, true_and, allowed]
  constructor
  · intro hx a ha
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    rintro himage
    obtain ⟨v, hv, rfl⟩ := mem_image.mp himage
    exact hx (mem_add.mpr ⟨x - v, ha, v, hv, sub_add_cancel _ _⟩)
  · intro h hx
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_add.mp hx
    exact (mem_sdiff.mp (h ha)).2 (mem_image.mpr ⟨v, hv, add_sub_cancel_right _ _⟩)

private theorem card_allowed (P : Finset G) (x : G) :
    (allowed P x).card = Fintype.card G - P.card := by
  rw [allowed, card_sdiff_of_subset (subset_univ _), card_univ]
  congr 1
  exact card_image_of_injOn fun _ _ _ _ h ↦ sub_right_inj.mp h

omit [Fintype G] in
private theorem mem_add_singleton_iff_sub_mem {A : Finset G} {t x : G} :
    x ∈ A + {t} ↔ x - t ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_add.mp hx
    simpa only [mem_singleton.mp hv, add_sub_cancel_right] using ha
  · intro hx
    exact mem_add.mpr ⟨x - t, hx, t, mem_singleton_self _, sub_add_cancel _ _⟩

omit [AddCommGroup G] in
private theorem sum_card_eq_sum_card_filter {ι : Type*} (S : Finset ι)
    (F : ι → Finset G) :
    ∑ a ∈ S, (F a).card = ∑ x ∈ (univ : Finset G), (S.filter (fun a ↦ x ∈ F a)).card := by
  classical
  calc
    _ = ∑ a ∈ S, ∑ x ∈ (univ : Finset G), (if x ∈ F a then (1 : ℕ) else 0) := by
      refine sum_congr rfl fun a _ ↦ ?_
      rw [← sum_filter]
      simp
    _ = ∑ x ∈ (univ : Finset G), ∑ a ∈ S, (if x ∈ F a then (1 : ℕ) else 0) := sum_comm
    _ = _ := by
      refine sum_congr rfl fun x _ ↦ ?_
      rw [← sum_filter]
      simp

private theorem filter_powersetCard_mem {α : Type*} [DecidableEq α]
    (S : Finset α) {x : α} (hx : x ∈ S) (n : ℕ) :
    ((S.powersetCard (n + 1)).filter (fun A ↦ x ∈ A)).card =
      (S.card - 1).choose n := by
  have hfilter : (S.powersetCard (n + 1)).filter (fun A ↦ x ∈ A) =
      ((S.erase x).powersetCard n).image (insert x) := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hAS, hcard⟩, hAx⟩
      refine ⟨A.erase x, ⟨?_, ?_⟩, insert_erase hAx⟩
      · intro a ha
        exact mem_erase.mpr ⟨(mem_erase.mp ha).1, hAS (mem_erase.mp ha).2⟩
      · rw [card_erase_of_mem hAx, hcard, Nat.add_sub_cancel]
    · rintro ⟨B, ⟨hBS, hcard⟩, rfl⟩
      refine ⟨⟨insert_subset hx (hBS.trans (erase_subset _ _)), ?_⟩, mem_insert_self _ _⟩
      rw [card_insert_of_notMem (fun h ↦ notMem_erase x S (hBS h)), hcard]
  rw [hfilter, card_image_of_injOn, card_powersetCard, card_erase_of_mem hx]
  intro A hA B hB h
  have hAx : x ∉ A := fun ha ↦ notMem_erase x S ((mem_powersetCard.mp hA).1 ha)
  have hBx : x ∉ B := fun hb ↦ notMem_erase x S ((mem_powersetCard.mp hB).1 hb)
  simpa only [erase_insert hAx, erase_insert hBx] using congrArg (fun U ↦ U.erase x) h

/-- Exact sum of uncovered cardinalities over the uniform `k`-subset sample space. -/
theorem sum_card_uncovered {p : ℕ} [NeZero p] (k : ℕ) (P : Finset (ZMod p)) :
    ∑ A ∈ (univ : Finset (ZMod p)).powersetCard k, (uncovered A P).card =
      p * (p - P.card).choose k := by
  rw [sum_card_eq_sum_card_filter]
  have hf (x : ZMod p) :
      (((univ : Finset (ZMod p)).powersetCard k).filter
        (fun A ↦ x ∈ uncovered A P)) = (allowed P x).powersetCard k := by
    ext A
    simp [mem_uncovered_iff_subset_allowed, and_comm]
  simp only [hf, card_powersetCard, card_allowed, ZMod.card, sum_const, card_univ, nsmul_eq_mul,
    Nat.cast_id]

/-- Exact sum of uncovered hits at a fixed outside center over the uniform
`k`-subset sample space. -/
theorem sum_card_outsideHits {p k : ℕ} [NeZero p] (P : Finset (ZMod p)) {t : ZMod p}
    (ht : t ∉ P) (hk : 1 ≤ k) :
    ∑ A ∈ (univ : Finset (ZMod p)).powersetCard k, (outsideHits A P t).card =
      p * (p - 1 - P.card).choose (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [sum_card_eq_sum_card_filter]
  have hf (x : ZMod p) :
      (((univ : Finset (ZMod p)).powersetCard (n + 1)).filter
        (fun A ↦ x ∈ outsideHits A P t)) =
        ((allowed P x).powersetCard (n + 1)).filter (fun A ↦ x - t ∈ A) := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, outsideHits, mem_inter,
      mem_add_singleton_iff_sub_mem, mem_uncovered_iff_subset_allowed]
    exact ⟨fun ⟨hc, ha, hs⟩ ↦ ⟨⟨hs, hc⟩, ha⟩, fun ⟨⟨hs, hc⟩, ha⟩ ↦ ⟨hc, ha, hs⟩⟩
  have hx (x : ZMod p) : x - t ∈ allowed P x := by
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    rintro hm
    obtain ⟨v, hv, he⟩ := mem_image.mp hm
    exact ht (sub_right_inj.mp he ▸ hv)
  simp only [hf, filter_powersetCard_mem _ (hx _), card_allowed, ZMod.card,
    Nat.sub_right_comm p P.card 1, Nat.succ_sub_one, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]

/-- Regularity bounds the intersection with every left translate of `P`. -/
def OutsideRegular (B P : Finset G) (L : ℕ) : Prop :=
  ∀ v : G, (B ∩ ({v} + P)).card ≤ L

omit [Fintype G] in
private theorem card_translate_inter (B P : Finset G) (t v : G) :
    ((B + {t}) ∩ ({v} + P)).card = (B ∩ ({v - t} + P)).card := by
  have hshift : ({v - t} : Finset G) + P + {t} = {v} + P := by
    calc
      _ = ({v - t} : Finset G) + {t} + P := add_right_comm _ _ _
      _ = _ := by rw [singleton_add_singleton, sub_add_cancel]
  rw [← hshift, ← inter_add_singleton, card_add_singleton]

private theorem card_lost_outsideHits_le {B B' P : Finset G} {L : ℕ}
    (hB : OutsideRegular B P L) (t : G) :
    (outsideHits B P t \ outsideHits B' P t).card ≤
      (B \ B').card + L * (B' \ B).card := by
  let hits (v : G) := (B + {t}) ∩ ({v} + P)
  have hsub : outsideHits B P t \ outsideHits B' P t ⊆
      ((B \ B') + {t}) ∪ (B' \ B).biUnion hits := by
    intro x hx
    obtain ⟨hx, hx'⟩ := mem_sdiff.mp hx
    obtain ⟨hxB, hxH⟩ := mem_inter.mp hx
    by_cases hxB' : x ∈ B' + {t}
    · have hxP : x ∈ B' + P := by
        by_contra hxP
        exact hx' (mem_inter.mpr ⟨hxB', mem_sdiff.mpr ⟨mem_univ _, hxP⟩⟩)
      obtain ⟨v, hvB', a, ha, he⟩ := mem_add.mp hxP
      have hvB : v ∉ B := fun hvB ↦ (mem_sdiff.mp hxH).2 (mem_add.mpr ⟨v, hvB, a, ha, he⟩)
      apply mem_union_right
      exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hvB', hvB⟩,
        mem_inter.mpr ⟨hxB, mem_add.mpr ⟨v, mem_singleton_self _, a, ha, he⟩⟩⟩
    · apply mem_union_left
      rw [mem_add_singleton_iff_sub_mem] at hxB hxB' ⊢
      exact mem_sdiff.mpr ⟨hxB, hxB'⟩
  calc
    _ ≤ (((B \ B') + {t}) ∪ (B' \ B).biUnion hits).card := card_le_card hsub
    _ ≤ ((B \ B') + {t}).card + ((B' \ B).biUnion hits).card := card_union_le _ _
    _ ≤ (B \ B').card + ∑ v ∈ B' \ B, (hits v).card := by
      rw [card_add_singleton]
      exact Nat.add_le_add_left card_biUnion_le _
    _ ≤ (B \ B').card + ∑ _v ∈ B' \ B, L :=
      Nat.add_le_add_left (sum_le_sum fun v _ ↦ (card_translate_inter B P t v).le.trans
        (hB (v - t))) _
    _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

/-- On samples of equal size, the absolute difference of the two hit counts is
at most `(1 + L) * (B \ B').card` when both samples are regular. -/
theorem dist_card_outsideHits_le {B B' P : Finset G} {L : ℕ}
    (hsize : B.card = B'.card) (hB : OutsideRegular B P L) (hB' : OutsideRegular B' P L)
    (t : G) :
    Nat.dist (outsideHits B P t).card (outsideHits B' P t).card ≤
      (1 + L) * (B \ B').card := by
  have hd : (B \ B').card = (B' \ B).card := card_sdiff_comm hsize
  have h : (outsideHits B P t \ outsideHits B' P t).card ≤ (1 + L) * (B \ B').card := by
    simpa only [Nat.add_mul, Nat.one_mul, ← hd] using
      (card_lost_outsideHits_le (B' := B') hB t)
  have h' : (outsideHits B' P t \ outsideHits B P t).card ≤ (1 + L) * (B \ B').card := by
    simpa only [Nat.add_mul, Nat.one_mul, ← hd] using
      (card_lost_outsideHits_le (B' := B) hB' t)
  rcases le_total (outsideHits B P t).card (outsideHits B' P t).card with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (le_card_sdiff _ _).trans h'
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (le_card_sdiff _ _).trans h

/-- Every uncovered point of a cover is hit by some center in `T \ P`. -/
theorem card_uncovered_le_sum_card_outsideHits (A P T : Finset G)
    (hcover : A + T = univ) :
    (uncovered A P).card ≤ ∑ t ∈ T \ P, (outsideHits A P t).card := by
  have hsub : uncovered A P ⊆ (T \ P).biUnion (outsideHits A P) := by
    intro x hx
    have hxT : x ∈ A + T := hcover ▸ mem_univ x
    obtain ⟨a, ha, t, ht, he⟩ := mem_add.mp hxT
    have htP : t ∉ P := fun htP ↦ (mem_sdiff.mp hx).2 (mem_add.mpr ⟨a, ha, t, htP, he⟩)
    exact mem_biUnion.mpr ⟨t, mem_sdiff.mpr ⟨ht, htP⟩,
      mem_inter.mpr ⟨mem_add.mpr ⟨a, ha, t, mem_singleton_self _, he⟩, hx⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- A pointwise cap on outside hits bounds how many holes the outside part of
any cover can account for. -/
theorem card_uncovered_le_card_outside_mul (A P T : Finset G)
    (hcover : A + T = univ) (C : ℕ)
    (hcap : ∀ t ∈ T \ P, (outsideHits A P t).card ≤ C) :
    (uncovered A P).card ≤ (T \ P).card * C := by
  calc
    _ ≤ ∑ t ∈ T \ P, (outsideHits A P t).card :=
      card_uncovered_le_sum_card_outsideHits A P T hcover
    _ ≤ ∑ _t ∈ T \ P, C := sum_le_sum hcap
    _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.cast_id]

/-- The two cardinality estimates in §1 force the stated lower bound for the
outside portion of every cover. -/
theorem le_card_outside_of_bounds (A P T : Finset G) (hcover : A + T = univ)
    {k : ℕ} {δ ρ : ℝ} (hk : 0 < k) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hholes : (1 - δ) * (Fintype.card G : ℝ) * ρ ≤ (uncovered A P).card)
    (hhits : ∀ t ∈ T \ P, ((outsideHits A P t).card : ℝ) ≤ (1 + δ) * k * ρ) :
    (1 - δ) / (1 + δ) * (Fintype.card G : ℝ) / k ≤ ((T \ P).card : ℝ) := by
  have hsum : ((uncovered A P).card : ℝ) ≤ ∑ t ∈ T \ P, ((outsideHits A P t).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (card_uncovered_le_sum_card_outsideHits A P T hcover)
  have hcap : (1 - δ) * (Fintype.card G : ℝ) * ρ ≤
      ((T \ P).card : ℝ) * ((1 + δ) * k * ρ) := by
    calc
      _ ≤ ((uncovered A P).card : ℝ) := hholes
      _ ≤ ∑ t ∈ T \ P, ((outsideHits A P t).card : ℝ) := hsum
      _ ≤ ∑ _t ∈ T \ P, (1 + δ) * k * ρ := sum_le_sum hhits
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hden : 0 < (1 + δ) * (k : ℝ) * ρ :=
    mul_pos (mul_pos (add_pos_of_pos_of_nonneg zero_lt_one hδ) (Nat.cast_pos.mpr hk)) hρ
  calc
    _ = ((1 - δ) * (Fintype.card G : ℝ)) / ((1 + δ) * k) := by
      rw [div_mul_eq_mul_div, div_div]
    _ = ((1 - δ) * (Fintype.card G : ℝ) * ρ) / ((1 + δ) * k * ρ) :=
      (mul_div_mul_right _ _ hρ.ne').symm
    _ ≤ _ := (div_le_iff₀ hden).mpr hcap

end Green39

#print axioms Green39.sum_card_uncovered
#print axioms Green39.sum_card_outsideHits
#print axioms Green39.dist_card_outsideHits_le
#print axioms Green39.card_uncovered_le_sum_card_outsideHits
#print axioms Green39.card_uncovered_le_card_outside_mul
#print axioms Green39.le_card_outside_of_bounds

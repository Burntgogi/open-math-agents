import FormalConjectures.GreensOpenProblems.«39»
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Private incidences in a Green 39 translate cover

The deterministic estimates in section 2 of `overnight-astra/review/one-percent.md`.
The cover equation is `A + T = Finset.univ`, as in `Green39.proportionCoverable`.
-/

open scoped BigOperators Pointwise

namespace Green39

variable {p : ℕ}

/-- The incidence of label `a` at center `t` is also covered at another center of `T`. -/
def NonprivateAt (A T : Finset (ZMod p)) (a t : ZMod p) : Prop :=
  ∃ b ∈ A, ∃ u ∈ T, u ≠ t ∧ b + u = a + t

/-- Labels in `L` that are nonprivate at `t` relative to the full sets `A` and `T`. -/
noncomputable def nonprivateLabels (A T L : Finset (ZMod p)) (t : ZMod p) :
    Finset (ZMod p) := by
  classical
  exact L.filter (fun a => NonprivateAt A T a t)

@[simp] theorem mem_nonprivateLabels {A T L : Finset (ZMod p)} {a t : ZMod p} :
    a ∈ nonprivateLabels A T L t ↔ a ∈ L ∧ NonprivateAt A T a t := by
  classical
  simp [nonprivateLabels]

private theorem card_filter_product {α β : Type*} (L : Finset α) (C : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    ((L ×ˢ C).filter fun i => P i.1 i.2).card =
      ∑ a ∈ L, (C.filter fun t => P a t).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_group_le_card_mul [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) : p ≤ A.card * T.card := by
  calc
    p = (A + T).card := by simp [hcover, ZMod.card]
    _ ≤ A.card * T.card := Finset.card_add_le

/-- A point with multiplicity `m` contributes either zero or at most `2 * (m - 1)`
nonprivate incidences. Sum this estimate over the covered group. -/
theorem total_nonprivate_incidence_le [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) :
    (∑ t ∈ T, (nonprivateLabels A T A t).card) ≤ 2 * (A.card * T.card - p) := by
  classical
  let point : ZMod p × ZMod p → ZMod p := fun i => i.2 + i.1
  let I := T ×ˢ A
  let J := I.filter (fun i => NonprivateAt A T i.2 i.1)
  let m := fun x => (I.filter (fun i => point i = x)).card
  let n := fun x => (J.filter (fun i => point i = x)).card
  have hJ : J.card = ∑ t ∈ T, (nonprivateLabels A T A t).card :=
    card_filter_product T A (fun t a => NonprivateAt A T a t)
  have hm : I.card = ∑ x, m x :=
    Finset.card_eq_sum_card_fiberwise (f := point) (fun _ _ => Finset.mem_univ _)
  have hn : J.card = ∑ x, n x :=
    Finset.card_eq_sum_card_fiberwise (f := point) (fun _ _ => Finset.mem_univ _)
  have hpoint : ∀ x, n x + 2 ≤ 2 * m x := by
    intro x
    have hpos : 0 < m x := by
      have hx : x ∈ A + T := by
        rw [hcover]
        exact Finset.mem_univ x
      obtain ⟨a, ha, t, ht, hat⟩ := Finset.mem_add.mp hx
      exact Finset.card_pos.mpr
        ⟨(t, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, ha⟩, hat⟩⟩
    have hle : n x ≤ m x := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨hj, hix⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hix⟩
    by_cases hmultiple : 1 < m x
    · omega
    · have hzero : n x = 0 := by
        by_contra hne
        obtain ⟨⟨t, a⟩, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
        obtain ⟨hj, hax⟩ := Finset.mem_filter.mp hi
        obtain ⟨hat, hb⟩ := Finset.mem_filter.mp hj
        obtain ⟨b, hbA, u, huT, hut, hbu⟩ := hb
        have htwo : 1 < m x :=
          Finset.one_lt_card.mpr ⟨(u, b),
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huT, hbA⟩, hbu.trans hax⟩,
            (t, a), Finset.mem_filter.mpr ⟨hat, hax⟩,
            fun h => hut (congrArg Prod.fst h)⟩
        exact hmultiple htwo
      omega
  have hsum : (∑ x, (n x + 2)) ≤ ∑ x, 2 * m x :=
    Finset.sum_le_sum (fun x _ => hpoint x)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hn, ← hm] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card,
    I, Finset.card_product] at hsum
  change J.card + p * 2 ≤ 2 * (T.card * A.card) at hsum
  rw [← hJ]
  rw [Nat.mul_comm T.card A.card] at hsum
  have hcovered := card_group_le_card_mul hcover
  omega

private theorem total_nonprivate_incidence_le_real [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) :
    ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤
      2 * ((A.card : ℝ) * T.card - p) := by
  have htotal : ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤
      ((2 * (A.card * T.card - p) : ℕ) : ℝ) := by
    exact_mod_cast total_nonprivate_incidence_le hcover
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (card_group_le_card_mul hcover)]
    using htotal

/-- Centers of `T` with at most `threshold` nonprivate labels in the full set `A`. -/
noncomputable def nearPrivateCenters (A T : Finset (ZMod p)) (threshold : ℝ) :
    Finset (ZMod p) := by
  classical
  exact T.filter (fun t => ((nonprivateLabels A T A t).card : ℝ) ≤ threshold)

@[simp] theorem mem_nearPrivateCenters {A T : Finset (ZMod p)} {t : ZMod p} {threshold : ℝ} :
    t ∈ nearPrivateCenters A T threshold ↔
      t ∈ T ∧ ((nonprivateLabels A T A t).card : ℝ) ≤ threshold := by
  classical
  simp [nearPrivateCenters]

/-- Averaging bounds the number of centers above the nonprivate-label threshold. -/
theorem card_nearPrivateCenters_ge [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (T.card : ℝ) - 2 * ((A.card : ℝ) * T.card - p) / threshold ≤
      (nearPrivateCenters A T threshold).card := by
  classical
  let good := nearPrivateCenters A T threshold
  let bad := T \ good
  have hgood : good ⊆ T := Finset.filter_subset _ _
  have hcount : (bad.card : ℝ) + good.card = T.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hgood
  have hsum : (bad.card : ℝ) * threshold ≤
      ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    calc
      (bad.card : ℝ) * threshold = ∑ _t ∈ bad, threshold := by simp
      _ ≤ ∑ t ∈ bad, ((nonprivateLabels A T A t).card : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨htT, hn⟩ := Finset.mem_sdiff.mp ht
        apply le_of_lt
        apply lt_of_not_ge
        intro h
        exact hn (mem_nearPrivateCenters.mpr ⟨htT, h⟩)
      _ ≤ ∑ t ∈ T, ((nonprivateLabels A T A t).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
  have hbad := (le_div_iff₀ hthreshold).mpr (hsum.trans (total_nonprivate_incidence_le_real hcover))
  linarith

/-- For a one-percent cover, at most `0.02 * p` incidences are nonprivate. -/
theorem total_nonprivate_incidence_onePercent [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) (hk : 0 < A.card)
    (hsmall : (T.card : ℝ) ≤ 1.01 * p / A.card) :
    ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤ 0.02 * p := by
  have hk' : (0 : ℝ) < A.card := by exact_mod_cast hk
  have hsmall' := (le_div_iff₀ hk').mp hsmall
  nlinarith only [hsmall', total_nonprivate_incidence_le_real hcover]

/-- The section 2 bounds for the number of centers with at most `0.0225 * |A|`
nonprivate labels. The square bound applies in particular to `|A| = Nat.sqrt p`. -/
theorem card_nearPrivateCenters_onePercent [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) (hk : 0 < A.card) (hsquare : A.card ^ 2 ≤ p)
    (hsmall : (T.card : ℝ) ≤ 1.01 * p / A.card) :
    let good := nearPrivateCenters A T (0.0225 * A.card)
    (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ≤ good.card ∧
      (p : ℝ) / (9 * A.card) ≤ (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ∧
      (A.card : ℝ) / 9 ≤ (p : ℝ) / (9 * A.card) := by
  have hk' : (0 : ℝ) < A.card := by exact_mod_cast hk
  have hthreshold : (0 : ℝ) < 0.0225 * A.card := by positivity
  have hsmall' := (le_div_iff₀ hk').mp hsmall
  have hcover' : (p : ℝ) ≤ (T.card : ℝ) * A.card := by
    rw [mul_comm]
    exact_mod_cast card_group_le_card_mul hcover
  have hsquare' : (A.card : ℝ) ^ 2 ≤ p := by exact_mod_cast hsquare
  refine ⟨?_, ?_, ?_⟩
  · calc
      (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ≤
          (T.card : ℝ) - 2 * ((A.card : ℝ) * T.card - p) / (0.0225 * A.card) := by
        apply sub_le_sub_left
        apply (div_le_div_iff_of_pos_right hthreshold).mpr
        nlinarith only [hsmall']
      _ ≤ _ := card_nearPrivateCenters_ge hcover hthreshold
  · have hlow : (p : ℝ) / A.card ≤ T.card := (div_le_iff₀ hk').mpr hcover'
    have heq : (p : ℝ) / (9 * A.card) + 0.02 * p / (0.0225 * A.card) = p / A.card := by
      field_simp
      ring
    linarith only [hlow, heq]
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 9 * A.card)]
    nlinarith only [hsquare']

/-- Private incidences in `A₁ × R` give distinct points of `A₁ + R`. -/
theorem card_add_ge_of_nonprivate_bound {A T A₁ R : Finset (ZMod p)}
    (hA₁ : A₁ ⊆ A) (hR : R ⊆ T) {bound : ℝ}
    (hbound : ∀ t ∈ R, ((nonprivateLabels A T A₁ t).card : ℝ) ≤ bound) :
    ((A₁.card : ℝ) - bound) * R.card ≤ (A₁ + R).card := by
  classical
  let I := (R ×ˢ A₁).filter (fun i => i.2 ∉ nonprivateLabels A T A₁ i.1)
  have hinj : I.card ≤ (A₁ + R).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.2 + i.1)
    · intro i hi
      obtain ⟨hr, ha⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hi).1
      exact Finset.add_mem_add ha hr
    · rintro ⟨t, a⟩ ht ⟨u, b⟩ hu heq
      obtain ⟨ht', hpriv⟩ := Finset.mem_filter.mp ht
      obtain ⟨_, ha⟩ := Finset.mem_product.mp ht'
      obtain ⟨hu', hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
      have hut : u = t := by
        by_contra hne
        exact hpriv (mem_nonprivateLabels.mpr ⟨ha, b, hA₁ hb, u, hR hu', hne, heq.symm⟩)
      subst u
      have hab : a = b := add_right_cancel heq
      subst b
      rfl
  have hcard : I.card = ∑ t ∈ R, (A₁ \ nonprivateLabels A T A₁ t).card := by
    calc
      I.card = ∑ t ∈ R, (A₁.filter (fun a => a ∉ nonprivateLabels A T A₁ t)).card :=
        card_filter_product R A₁ (fun t a => a ∉ nonprivateLabels A T A₁ t)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_sdiff]
  have hinj' : (I.card : ℝ) ≤ (A₁ + R).card := by exact_mod_cast hinj
  rw [hcard, Nat.cast_sum] at hinj'
  refine le_trans ?_ hinj'
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.cast_card_sdiff (s := nonprivateLabels A T A₁ t) (t := A₁)
    (fun _ ha => (mem_nonprivateLabels.mp ha).1)]
  exact sub_le_sub_left (hbound t ht) _

/-- For disjoint label sets, every hit of `A₁ + R` by an `A₂` label at an `S` center
is a nonprivate incidence. The two sets of centers can overlap. -/
theorem sum_translate_inter_card_le_of_nonprivate_bound {A T A₁ A₂ R S : Finset (ZMod p)}
    (hA₁ : A₁ ⊆ A) (hdisjoint : Disjoint A₁ A₂) (hR : R ⊆ T) {bound : ℝ}
    (hbound : ∀ t ∈ S, ((nonprivateLabels A T A₂ t).card : ℝ) ≤ bound) :
    ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ (A₁ + R)).card : ℕ) : ℝ) ≤
      bound * S.card := by
  classical
  let U := A₁ + R
  have hslice (z : ZMod p) : ((({z} : Finset (ZMod p)) + S) ∩ U).card =
      (S.filter (fun t => z + t ∈ U)).card := by
    have himage : (S.filter (fun t => z + t ∈ U)).image (fun t => z + t) =
        (({z} : Finset (ZMod p)) + S) ∩ U := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter, Finset.mem_add,
        Finset.mem_singleton]
      constructor
      · rintro ⟨t, ⟨ht, hU⟩, rfl⟩
        exact ⟨⟨z, rfl, t, ht, rfl⟩, hU⟩
      · rintro ⟨⟨a, rfl, t, ht, rfl⟩, hU⟩
        exact ⟨t, ⟨ht, hU⟩, rfl⟩
    rw [← himage, Finset.card_image_of_injective _ (add_right_injective z)]
  have hswap : (∑ z ∈ A₂, (S.filter (fun t => z + t ∈ U)).card) =
      ∑ t ∈ S, (A₂.filter (fun z => z + t ∈ U)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  change ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
    bound * S.card
  simp_rw [hslice]
  rw [hswap, Nat.cast_sum, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro t ht
  refine le_trans ?_ (hbound t ht)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzA₂, hzU⟩ := Finset.mem_filter.mp hz
  obtain ⟨a, ha, u, hu, hau⟩ := Finset.mem_add.mp hzU
  have hut : u ≠ t := by
    intro heq
    subst u
    have haz : a = z := add_right_cancel hau
    exact Finset.disjoint_left.mp hdisjoint (haz ▸ ha) hzA₂
  exact mem_nonprivateLabels.mpr ⟨hzA₂, a, hA₁ ha, u, hR hu, hut, hau⟩

/-- Both inequalities (3) for a given balanced split. The per-half bound is `0.0114 * |A|`.
The hypotheses on `R` and `S` are independent. -/
theorem balanced_halves_bounds {A T A₁ A₂ R S : Finset (ZMod p)}
    (hsplit : A₁ ∪ A₂ = A) (hdisjoint : Disjoint A₁ A₂)
    (hbalance : A₁.card = A.card / 2) (hR : R ⊆ T) (_hS : S ⊆ T)
    (hR₁ : ∀ t ∈ R, ((nonprivateLabels A T A₁ t).card : ℝ) ≤ 0.0114 * A.card)
    (hS₂ : ∀ t ∈ S, ((nonprivateLabels A T A₂ t).card : ℝ) ≤ 0.0114 * A.card) :
    let U := A₁ + R
    (((A.card / 2 : ℕ) : ℝ) - 0.0114 * A.card) * R.card ≤ U.card ∧
      ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
        0.0114 * A.card * S.card := by
  have hA₁ : A₁ ⊆ A := by
    rw [← hsplit]
    exact Finset.subset_union_left
  refine ⟨?_, sum_translate_inter_card_le_of_nonprivate_bound hA₁ hdisjoint hR hS₂⟩
  rw [← hbalance]
  exact card_add_ge_of_nonprivate_bound hA₁ hR hR₁

end Green39

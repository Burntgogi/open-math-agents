import Mathlib
import FormalConjectures.GreensOpenProblems.«39»

/-!
# IID sampling for Green's problem 39

The uniform probability on `Fin k → ZMod p` is the joint law of `k` independent
uniform draws. Each `k`-element image has exactly `k!` injective orderings.
-/

open Filter Topology
open scoped Pointwise Classical

set_option autoImplicit false

namespace Green39.IID

noncomputable section

variable {p k : ℕ} [NeZero p]

/-- The set of values appearing in an ordered tuple. -/
def image (x : Fin k → ZMod p) : Finset (ZMod p) := Finset.univ.image x

/-- The space of `k`-element subsets of `ZMod p`. -/
def subsets (p k : ℕ) [NeZero p] : Finset (Finset (ZMod p)) :=
  Finset.univ.powersetCard k

/-- The tuples realizing an event. -/
def tuples (E : (Fin k → ZMod p) → Prop) : Finset (Fin k → ZMod p) :=
  Finset.univ.filter E

@[simp] theorem mem_tuples {E : (Fin k → ZMod p) → Prop} {x : Fin k → ZMod p} :
    x ∈ tuples E ↔ E x := by
  simp [tuples]

/-- The uniform probability of an event in the IID tuple space. -/
def probability (E : (Fin k → ZMod p) → Prop) : ℝ :=
  ((tuples E).card : ℝ) / (p : ℝ) ^ k

/-- The covering event used by `Green39.proportionCoverable`. -/
def Coverable (c : ℕ) (A : Finset (ZMod p)) : Prop :=
  ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ

theorem probability_nonneg (E : (Fin k → ZMod p) → Prop) : 0 ≤ probability E := by
  unfold probability
  positivity

theorem probability_mono {E F : (Fin k → ZMod p) → Prop} (h : ∀ x, E x → F x) :
    probability E ≤ probability F := by
  have hsub : tuples E ⊆ tuples F := fun x hx ↦ mem_tuples.mpr (h x (mem_tuples.mp hx))
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

theorem probability_add_compl (E : (Fin k → ZMod p) → Prop) :
    probability E + probability (fun x ↦ ¬ E x) = 1 := by
  have htotal : (Finset.univ : Finset (Fin k → ZMod p)).card = p ^ k := by
    rw [Finset.card_univ, Fintype.card_pi_const, ZMod.card]
  have hp : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hpos : 0 < (p : ℝ) ^ k := by positivity
  simp only [probability, tuples]
  rw [← add_div, ← Nat.cast_add,
    Finset.card_filter_add_card_filter_not, htotal, Nat.cast_pow, div_self hpos.ne']

/-- Every fixed `k`-element set is the image of exactly `k!` injective tuples. -/
theorem card_injective_image (A : Finset (ZMod p)) (hA : A.card = k) :
    (tuples (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ image x = A)).card =
      k.factorial := by
  let fiber := {x : Fin k → ZMod p // Function.Injective x ∧ image x = A}
  let e : fiber ≃ (Fin k ≃ ↥A) :=
    { toFun := fun x ↦ Equiv.ofBijective
        (fun i ↦ ⟨x.1 i, by
          have hx : x.1 i ∈ image x.1 := Finset.mem_image_of_mem x.1 (Finset.mem_univ i)
          exact (congrArg (fun B ↦ x.1 i ∈ B) x.2.2).mp hx⟩)
        ⟨fun _ _ h ↦ x.2.1 (congrArg Subtype.val h), fun a ↦ by
          have ha : a.1 ∈ image x.1 := (congrArg (fun B ↦ a.1 ∈ B) x.2.2).mpr a.2
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
          exact ⟨i, Subtype.ext hi⟩⟩
      invFun := fun f ↦ ⟨fun i ↦ (f i).1, fun _ _ h ↦ f.injective (Subtype.ext h), by
        ext a
        constructor
        · rintro ha
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
          exact (f i).2
        · intro ha
          obtain ⟨i, hi⟩ := f.surjective ⟨a, ha⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ Equiv.ext fun i ↦ Subtype.ext rfl }
  have hcard : Fintype.card (Fin k) = Fintype.card ↥A := by simp [hA]
  rw [tuples, ← Fintype.card_subtype, Fintype.card_congr e,
    Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

/-- Counting injective tuples with an image satisfying `Q` amounts to counting
`k`-element sets satisfying `Q`, with multiplicity `k!`. -/
theorem card_injective_and (Q : Finset (ZMod p) → Prop) :
    (tuples (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ Q (image x))).card =
      ((subsets p k).filter Q).card * k.factorial := by
  let S := tuples (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ Q (image x))
  let T := (subsets p k).filter Q
  change S.card = T.card * k.factorial
  have hmap : (S : Set (Fin k → ZMod p)).MapsTo image T := by
    intro x hx
    obtain ⟨hinj, hQ⟩ := mem_tuples.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simp [image, Finset.card_image_of_injective _ hinj]⟩, hQ⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    ∑ A ∈ T, (S.filter (fun x ↦ image x = A)).card = ∑ _A ∈ T, k.factorial := by
      apply Finset.sum_congr rfl
      intro A hA
      obtain ⟨hcard, hQ⟩ := Finset.mem_filter.mp hA
      have hf : S.filter (fun x ↦ image x = A) = tuples
          (fun x ↦ Function.Injective x ∧ image x = A) := by
        ext x
        simp only [S, tuples, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨h, he⟩ ↦ ⟨h.1, he⟩, fun ⟨hi, he⟩ ↦ ⟨⟨hi, he.symm ▸ hQ⟩, he⟩⟩
      rw [hf, card_injective_image _ (Finset.mem_powersetCard.mp hcard).2]
    _ = T.card * k.factorial := by simp

/-- The IID sample space contains exactly `p.choose k * k!` injective tuples. -/
theorem card_injective :
    (tuples (Function.Injective : (Fin k → ZMod p) → Prop)).card =
      p.choose k * k.factorial := by
  simpa [subsets, ZMod.card] using card_injective_and (p := p) (k := k) (fun _ ↦ True)

/-- A fixed pair of distinct coordinates agrees in exactly `p^(k-1)` tuples. -/
theorem card_eq_at_pair {i j : Fin k} (hij : i ≠ j) :
    (tuples (fun x : Fin k → ZMod p ↦ x i = x j)).card = p ^ (k - 1) := by
  let e : {x : Fin k → ZMod p // x i = x j} ≃ ({l : Fin k // l ≠ j} → ZMod p) :=
    { toFun := fun x l ↦ x.1 l.1
      invFun := fun f ↦ ⟨fun l ↦ if h : l = j then f ⟨i, hij⟩ else f ⟨l, h⟩, by
        simp [hij]⟩
      left_inv := fun x ↦ Subtype.ext (funext fun l ↦ by
        by_cases h : l = j
        · subst l
          simpa using x.2
        · simp [h])
      right_inv := fun f ↦ funext fun l ↦ by simp [l.2] }
  rw [tuples, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

/-- Pointwise union bound on the number of tuples with a collision. -/
theorem card_not_injective_le :
    (tuples (fun x : Fin k → ZMod p ↦ ¬ Function.Injective x)).card ≤
      k.choose 2 * p ^ (k - 1) := by
  let pairs := (Finset.univ : Finset (Fin k)).powersetCard 2
  let collide (s : Finset (Fin k)) := tuples
    (fun x : Fin k → ZMod p ↦ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ x i = x j)
  have hsubset : tuples (fun x : Fin k → ZMod p ↦ ¬ Function.Injective x) ⊆
      pairs.biUnion collide := by
    intro x hx
    have h := mem_tuples.mp hx
    rw [Function.Injective] at h
    push Not at h
    obtain ⟨i, j, he, hne⟩ := h
    refine Finset.mem_biUnion.mpr ⟨{i, j}, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
        Finset.card_eq_two.mpr ⟨i, j, hne, rfl⟩⟩
    · exact mem_tuples.mpr ⟨i, by simp, j, by simp, hne, he⟩
  refine (Finset.card_le_card hsubset).trans ?_
  have hbound : (pairs.biUnion collide).card ≤ pairs.card * p ^ (k - 1) := by
    apply Finset.card_biUnion_le_card_mul
    intro s hs
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    have he : collide {i, j} = tuples (fun x : Fin k → ZMod p ↦ x i = x j) := by
      ext x
      simp only [collide, tuples, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, b, hb, hab, h⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hab rfl).elim
        · exact h
        · exact h.symm
        · exact (hab rfl).elim
      · intro h
        exact ⟨i, by simp, j, by simp, hij, h⟩
    rw [he, card_eq_at_pair hij]
  simpa [pairs] using hbound

/-- The chance of any repeated coordinate is at most `choose k 2 / p`. -/
theorem probability_not_injective_le :
    probability (fun x : Fin k → ZMod p ↦ ¬ Function.Injective x) ≤
      (k.choose 2 : ℝ) / p := by
  rw [probability]
  have hp : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  by_cases hk : k = 0
  · subst k
    have h := card_not_injective_le (p := p) (k := 0)
    simp at h
    simp [h]
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
  have hpow : (p : ℝ) ^ k = (p : ℝ) ^ (k - 1) * p := by rw [← pow_succ, hk']
  calc
    _ ≤ ((k.choose 2 : ℝ) * (p : ℝ) ^ (k - 1)) / (p : ℝ) ^ k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_not_injective_le (p := p) (k := k)
    _ = (k.choose 2 : ℝ) / p := by
      rw [hpow]
      field_simp

theorem sqrt_choose_two_div_le_half : ((p.sqrt.choose 2 : ℕ) : ℝ) / p ≤ 1 / 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_iff₀ hp).mpr
  have hnat : p.sqrt.choose 2 * 2 ≤ p := by
    rw [Nat.choose_two_right]
    calc
      (p.sqrt * (p.sqrt - 1)) / 2 * 2 ≤ p.sqrt * (p.sqrt - 1) := Nat.div_mul_le_self _ _
      _ ≤ p.sqrt * p.sqrt := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ p := Nat.sqrt_le p
  have hreal : (p.sqrt.choose 2 : ℝ) * 2 ≤ p := by exact_mod_cast hnat
  linarith

/-- For `k = Nat.sqrt p`, at least half the tuples are injective. -/
theorem half_le_probability_injective :
    (1 / 2 : ℝ) ≤ probability (Function.Injective : (Fin p.sqrt → ZMod p) → Prop) := by
  have hsum := probability_add_compl (Function.Injective : (Fin p.sqrt → ZMod p) → Prop)
  have hcollision := (probability_not_injective_le (p := p) (k := p.sqrt)).trans
    (sqrt_choose_two_div_le_half (p := p))
  linarith

/-- The joint probability of injectivity and an image event factors into the
uniform subset proportion and the probability of injectivity. -/
theorem probability_injective_and_eq (hk : k ≤ p) (Q : Finset (ZMod p) → Prop) :
    probability (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ Q (image x)) =
      ((subsets p k).filter Q).card / (p.choose k : ℝ) *
        probability (Function.Injective : (Fin k → ZMod p) → Prop) := by
  have hchoose : (p.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [probability, probability, card_injective_and, card_injective]
  push_cast
  field_simp [hchoose, hp]

/-- Conditioned on injectivity, the image is uniform on the `k`-element subsets. -/
theorem conditional_image_probability (hk : k ≤ p) (Q : Finset (ZMod p) → Prop) :
    probability (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ Q (image x)) /
        probability (Function.Injective : (Fin k → ZMod p) → Prop) =
      ((subsets p k).filter Q).card / (p.choose k : ℝ) := by
  have hpos : 0 < probability (Function.Injective : (Fin k → ZMod p) → Prop) := by
    rw [probability, card_injective]
    have hp : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have := Nat.choose_pos hk
    have := Nat.factorial_pos k
    positivity
  exact (div_eq_iff hpos.ne').mpr (probability_injective_and_eq hk Q)

theorem proportionCoverable_eq_div (hk : k ≤ p) (c : ℕ) :
    (Green39.proportionCoverable p k c : ℝ) =
      ((subsets p k).filter (Coverable c)).card / (p.choose k : ℝ) := by
  rw [Green39.proportionCoverable, dif_neg (NeZero.ne p), if_neg (not_lt_of_ge hk)]
  push_cast
  have hcard : (subsets p k).card = p.choose k := by simp [subsets]
  rw [← hcard]
  congr 3
  ext A
  simp [subsets, Coverable]

/-- The unconditional probability that an IID tuple is injective and its image
can cover using at most `c` translates. -/
def injectiveCoverableProbability (p k c : ℕ) [NeZero p] : ℝ :=
  probability (fun x : Fin k → ZMod p ↦ Function.Injective x ∧ Coverable c (image x))

/-- The unconditional probability that the image of an IID tuple can cover using
at most `c` translates. -/
def coverableProbability (p k c : ℕ) [NeZero p] : ℝ :=
  probability (fun x : Fin k → ZMod p ↦ Coverable c (image x))

theorem injectiveCoverableProbability_le (c : ℕ) :
    injectiveCoverableProbability p k c ≤ coverableProbability p k c :=
  probability_mono (fun _ h ↦ h.2)

theorem proportionCoverable_le_two_mul_injective (c : ℕ) :
    (Green39.proportionCoverable p p.sqrt c : ℝ) ≤
      2 * injectiveCoverableProbability p p.sqrt c := by
  have hle := Nat.sqrt_le_self p
  rw [proportionCoverable_eq_div hle, injectiveCoverableProbability,
    probability_injective_and_eq hle]
  have hnonneg : 0 ≤ (((subsets p p.sqrt).filter (Coverable c)).card : ℝ) /
      (p.choose p.sqrt : ℝ) := by positivity
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr (half_le_probability_injective (p := p)))]

theorem proportionCoverable_le_two_mul (c : ℕ) :
    (Green39.proportionCoverable p p.sqrt c : ℝ) ≤ 2 * coverableProbability p p.sqrt c :=
  (proportionCoverable_le_two_mul_injective c).trans
    (mul_le_mul_of_nonneg_left (injectiveCoverableProbability_le c) (by norm_num))

end

/-- The IID joint event at the precise sample size and budget of `variant_101`. -/
noncomputable def variant101InjectiveProbability (p : {q : ℕ // q.Prime}) : ℝ :=
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  let k := Nat.sqrt p
  let c := ⌊1.01 * (k : ℝ)⌋₊
  injectiveCoverableProbability p k c

/-- The IID covering event at the precise sample size and budget of `variant_101`. -/
noncomputable def variant101Probability (p : {q : ℕ // q.Prime}) : ℝ :=
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  let k := Nat.sqrt p
  let c := ⌊1.01 * (k : ℝ)⌋₊
  coverableProbability p k c

/-- A vanishing IID joint probability disproves the exact upstream proposition. -/
theorem not_variant_101_of_injective_tendsto_zero
    (h : Tendsto variant101InjectiveProbability atTop (𝓝 0)) :
    ¬ type_of% @Green39.green_39.variant_101 := by
  intro hupstream
  let f (p : {q : ℕ // q.Prime}) : ℝ :=
    let k := Nat.sqrt p
    let c := ⌊1.01 * (k : ℝ)⌋₊
    (Green39.proportionCoverable p k c : ℝ)
  change Tendsto f atTop (𝓝 1) at hupstream
  have hupper : Tendsto (fun p ↦ 2 * variant101InjectiveProbability p) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul h
  have hzero : Tendsto f atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro p
      let : NeZero p.val := ⟨p.property.ne_zero⟩
      dsimp [f]
      rw [proportionCoverable_eq_div (Nat.sqrt_le_self p.val)]
      positivity
    · intro p
      let : NeZero p.val := ⟨p.property.ne_zero⟩
      exact proportionCoverable_le_two_mul_injective _
  let : Nonempty {q : ℕ // q.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
  have h01 := tendsto_nhds_unique hzero hupstream
  exact zero_ne_one h01

/-- It also suffices to bound the IID covering event alone. -/
theorem not_variant_101_of_tendsto_zero
    (h : Tendsto variant101Probability atTop (𝓝 0)) :
    ¬ type_of% @Green39.green_39.variant_101 := by
  apply not_variant_101_of_injective_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
  · intro p
    let : NeZero p.val := ⟨p.property.ne_zero⟩
    exact probability_nonneg _
  · intro p
    let : NeZero p.val := ⟨p.property.ne_zero⟩
    exact injectiveCoverableProbability_le _

end Green39.IID

#print axioms Green39.IID.card_injective_image
#print axioms Green39.IID.card_injective_and
#print axioms Green39.IID.card_eq_at_pair
#print axioms Green39.IID.probability_not_injective_le
#print axioms Green39.IID.conditional_image_probability
#print axioms Green39.IID.proportionCoverable_le_two_mul_injective
#print axioms Green39.IID.proportionCoverable_le_two_mul
#print axioms Green39.IID.not_variant_101_of_injective_tendsto_zero
#print axioms Green39.IID.not_variant_101_of_tendsto_zero

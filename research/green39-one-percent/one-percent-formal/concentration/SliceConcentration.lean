import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Exchange bounded differences on a finite slice

The sample is a uniformly chosen `k`-subset of a finite population. The proof
exposes one element at a time and couples two choices by a transposition.
This is the concentration argument in §1 of `overnight-astra/review/one-percent.md`.
-/

open MeasureTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace Green39.Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The arithmetic mean over a finite sample space. -/
def mean (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, f a) / s.card

/-- Expectation under the uniform law on the `k`-element subsets of `s`. -/
def sliceMean (s : Finset α) (k : ℕ) (f : Finset α → ℝ) : ℝ :=
  mean (s.powersetCard k) f

/-- Two elements of the slice at exchange distance at most one have observable
values within `L` of each other. -/
def ExchangeLipschitz (s : Finset α) (k : ℕ) (f : Finset α → ℝ) (L : ℝ) : Prop :=
  ∀ A ∈ s.powersetCard k, ∀ B ∈ s.powersetCard k,
    (A \ B).card ≤ 1 → |f A - f B| ≤ L

private theorem mem_slice_insert {s A : Finset α} {k : ℕ} {x : α} (hx : x ∈ s)
    (hA : A ∈ (s.erase x).powersetCard k) :
    insert x A ∈ s.powersetCard (k + 1) := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
  have hnot : x ∉ A := fun h ↦ Finset.notMem_erase x s (hsub h)
  exact Finset.mem_powersetCard.mpr
    ⟨Finset.insert_subset_iff.mpr ⟨hx, hsub.trans (Finset.erase_subset _ _)⟩,
      by rw [Finset.card_insert_of_notMem hnot, hcard]⟩

/-- Exposing an element preserves the exchange bound on the remaining slice. -/
theorem ExchangeLipschitz.insert {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hf : ExchangeLipschitz s (k + 1) f L) {x : α} (hx : x ∈ s) :
    ExchangeLipschitz (s.erase x) k (fun A ↦ f (insert x A)) L := by
  intro A hA B hB hd
  apply hf _ (mem_slice_insert hx hA) _ (mem_slice_insert hx hB)
  refine (Finset.card_le_card ?_).trans hd
  intro z hz
  simp only [Finset.mem_sdiff, Finset.mem_insert] at hz ⊢
  tauto

private theorem sum_slice_insert (s : Finset α) (k : ℕ) (f : Finset α → ℝ)
    {x : α} (hx : x ∈ s) :
    ∑ A ∈ (s.erase x).powersetCard k, f (insert x A) =
      ∑ B ∈ (s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B), f B := by
  refine Finset.sum_bij (fun A _ ↦ insert x A) (fun A hA ↦ ?_) (fun A hA B hB h ↦ ?_)
    (fun B hB ↦ ?_) (fun _ _ ↦ rfl)
  · simp [mem_slice_insert hx hA]
  · have erase_insert (C : Finset α) (hC : C ∈ (s.erase x).powersetCard k) :
        (insert x C).erase x = C :=
      Finset.erase_insert <| fun hxC ↦ Finset.notMem_erase x s ((Finset.mem_powersetCard.mp hC).1 hxC)
    simpa only [erase_insert A hA, erase_insert B hB] using congrArg (fun C ↦ C.erase x) h
  · obtain ⟨hB, hxB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
    refine ⟨B.erase x, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.insert_erase hxB⟩
    · exact Finset.erase_subset_erase _ hsub
    · rw [Finset.card_erase_of_mem hxB, hcard, Nat.add_sub_cancel]

private theorem sum_slice_first (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    (∑ x ∈ s, ∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) =
      (k + 1 : ℝ) * ∑ B ∈ s.powersetCard (k + 1), f B := by
  calc
    _ = ∑ x ∈ s, ∑ B ∈ s.powersetCard (k + 1), if x ∈ B then f B else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sum_slice_insert s k f hx, Finset.sum_filter]
    _ = ∑ B ∈ s.powersetCard (k + 1), ∑ x ∈ s, if x ∈ B then f B else 0 :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
      have hfilter : s.filter (fun x ↦ x ∈ B) = B := by
        ext x
        exact Finset.mem_filter.trans ⟨And.right, fun hx ↦ ⟨hsub hx, hx⟩⟩
      rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_add,
        Nat.cast_one]

/-- A uniformly chosen first element, followed by a uniform completion, gives
the uniform law on the full slice. -/
theorem sliceMean_succ (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    sliceMean s (k + 1) f =
      mean s (fun x ↦ sliceMean (s.erase x) k (fun A ↦ f (insert x A))) := by
  let d := (s.card - 1).choose k
  have hcard (x : α) (hx : x ∈ s) : ((s.erase x).powersetCard k).card = d := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hx]
  have hcounts : (s.card : ℝ) * d = (k + 1 : ℝ) * (s.powersetCard (k + 1)).card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] using
      calc
        (s.card : ℝ) * d = ∑ x ∈ s, (∑ _A ∈ (s.erase x).powersetCard k, (1 : ℝ)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          calc
            _ = ∑ _x ∈ s, (d : ℝ) := by simp [nsmul_eq_mul]
            _ = _ := Finset.sum_congr rfl (fun x hx ↦ by rw [hcard x hx])
        _ = _ := sum_slice_first s k (fun _ ↦ 1)
  unfold sliceMean mean
  have hsum :
      (∑ x ∈ s, (∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) /
        ((s.erase x).powersetCard k).card) =
      (∑ x ∈ s, ∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) / d := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun x hx ↦ by rw [hcard x hx])
  rw [hsum, sum_slice_first, div_div, mul_comm (d : ℝ), hcounts, mul_div_mul_left _ _ (by positivity)]

private theorem sliceMean_insert_eq_mean_filter (s : Finset α) (k : ℕ)
    (f : Finset α → ℝ) {x : α} (hx : x ∈ s) :
    sliceMean (s.erase x) k (fun A ↦ f (insert x A)) =
      mean ((s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)) f := by
  have hcard :
      (((s.erase x).powersetCard k).card : ℝ) =
        (((s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)).card : ℝ) := by
    simpa using sum_slice_insert s k (fun _ ↦ 1) hx
  unfold sliceMean mean
  rw [sum_slice_insert s k f hx, hcard]

private def swapSet (x y : α) (A : Finset α) : Finset α :=
  A.map (Equiv.swap x y).toEmbedding

private theorem mem_swapSet {x y z : α} {A : Finset α} :
    z ∈ swapSet x y A ↔ Equiv.swap x y z ∈ A := by
  rw [swapSet, Finset.mem_map]
  exact ⟨fun ⟨a, ha, haz⟩ ↦ by
    change Equiv.swap x y a = z at haz
    simpa [← haz] using ha,
    fun hz ↦ ⟨Equiv.swap x y z, hz, Equiv.swap_apply_self _ _ _⟩⟩

private theorem swapSet_swapSet (x y : α) (A : Finset α) :
    swapSet x y (swapSet x y A) = A := by
  ext z
  simp only [mem_swapSet, Equiv.swap_apply_self]

private theorem swap_mem {s : Finset α} {x y z : α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) : Equiv.swap x y z ∈ s := by
  by_cases hzx : z = x
  · simpa [hzx] using hy
  by_cases hzy : z = y
  · simpa [hzy] using hx
  simpa [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

private theorem swapSet_mem_filter {s A : Finset α} {k : ℕ} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s)
    (hA : A ∈ (s.powersetCard k).filter (fun B ↦ x ∈ B)) :
    swapSet x y A ∈ (s.powersetCard k).filter (fun B ↦ y ∈ B) := by
  obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have hm := swap_mem hx hy (hsub (mem_swapSet.mp hz))
    simpa only [Equiv.swap_apply_self] using hm
  · simpa [swapSet] using hcard
  · simpa only [mem_swapSet, Equiv.swap_apply_right] using hxA

private theorem card_sdiff_swapSet_le_one {x y : α} {A : Finset α} (hx : x ∈ A) :
    (A \ swapSet x y A).card ≤ 1 := by
  have hsub : A \ swapSet x y A ⊆ {x} := by
    intro z hz
    obtain ⟨hzA, hzswap⟩ := Finset.mem_sdiff.mp hz
    by_contra hzx
    have hne : z ≠ x := by simpa using hzx
    apply hzswap
    rw [mem_swapSet]
    by_cases hzy : z = y
    · simpa [hzy] using hx
    simpa [Equiv.swap_apply_of_ne_of_ne hne hzy] using hzA
  simpa using Finset.card_le_card hsub

private theorem abs_mean_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} (hf : ∀ x ∈ s, |f x| ≤ L) : |mean s f| ≤ L := by
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [mean, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ s, L := Finset.sum_le_sum hf
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- Any two first choices give conditional means within one exchange bound.
The coupling applies the same transposition to the entire completion. -/
theorem abs_sliceMean_insert_sub_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k + 1 ≤ s.card) (hf : ExchangeLipschitz s (k + 1) f L)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    |sliceMean (s.erase x) k (fun A ↦ f (insert x A)) -
      sliceMean (s.erase y) k (fun A ↦ f (insert y A))| ≤ L := by
  rw [sliceMean_insert_eq_mean_filter s k f hx, sliceMean_insert_eq_mean_filter s k f hy]
  let S := (s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)
  let T := (s.powersetCard (k + 1)).filter (fun B ↦ y ∈ B)
  change |mean S f - mean T f| ≤ L
  have hS : S.Nonempty := by
    have hle : k ≤ (s.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨A, hA⟩ := Finset.powersetCard_nonempty.mpr hle
    exact ⟨insert x A, Finset.mem_filter.mpr ⟨mem_slice_insert hx hA, Finset.mem_insert_self _ _⟩⟩
  have sum_swap (g : Finset α → ℝ) : ∑ A ∈ S, g (swapSet x y A) = ∑ B ∈ T, g B := by
    refine Finset.sum_bij (fun A _ ↦ swapSet x y A) (fun A hA ↦ swapSet_mem_filter hx hy hA)
      (fun A _ B _ h ↦ ?_) (fun B hB ↦ ?_) (fun _ _ ↦ rfl)
    · simpa only [swapSet_swapSet] using congrArg (swapSet x y) h
    · have hs : swapSet x y B = swapSet y x B := by simp [swapSet, Equiv.swap_comm x y]
      exact ⟨swapSet x y B, hs.symm ▸ swapSet_mem_filter hy hx hB, swapSet_swapSet x y B⟩
  have hcard : (S.card : ℝ) = (T.card : ℝ) := by
    simpa using sum_swap (fun _ ↦ 1)
  have hdiff : mean S f - mean T f = mean S (fun A ↦ f A - f (swapSet x y A)) := by
    rw [mean, mean, mean, Finset.sum_sub_distrib, sum_swap, hcard, sub_div]
  rw [hdiff]
  apply abs_mean_le hS
  intro A hA
  obtain ⟨hAA, hxA⟩ := Finset.mem_filter.mp hA
  exact hf A hAA _ (Finset.mem_filter.mp (swapSet_mem_filter hx hy hA)).1
    (card_sdiff_swapSet_le_one (y := y) hxA)

private theorem mean_congr {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ x ∈ s, f x = g x) : mean s f = mean s g := by
  unfold mean
  rw [Finset.sum_congr rfl h]

private theorem mean_mono {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : mean s f ≤ mean s g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem mean_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (c : ℝ) :
    mean s (fun _ ↦ c) = c := by
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [mean, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀ _ hpos.ne']

private theorem mean_const_mul {ι : Type*} (s : Finset ι) (a : ℝ) (f : ι → ℝ) :
    mean s (fun x ↦ a * f x) = a * mean s f := by
  rw [mean, ← Finset.mul_sum, mul_div_assoc, mean]

private theorem mean_sub {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    mean s (fun x ↦ f x - g x) = mean s f - mean s g := by
  unfold mean
  rw [Finset.sum_sub_distrib, sub_div]

private theorem abs_sub_mean_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} {x : ι} (hx : x ∈ s)
    (h : ∀ a ∈ s, ∀ b ∈ s, |f a - f b| ≤ L) : |f x - mean s f| ≤ L := by
  rw [← mean_const hs (f x), ← mean_sub]
  exact abs_mean_le hs (h x hx)

private theorem mean_exp_centered_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ s, |f x - mean s f| ≤ L) (t : ℝ) :
    mean s (fun x ↦ Real.exp (t * (f x - mean s f))) ≤ Real.exp (L ^ 2 * t ^ 2 / 2) := by
  let : MeasurableSpace ↥s := ⊤
  let : Nonempty ↥s := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨⟨x, hx⟩⟩
  let p := PMF.uniformOfFintype ↥s
  have integral_mean (g : ι → ℝ) :
      (∫ x : ↥s, g x ∂p.toMeasure) = mean s g := by
    rw [PMF.integral_eq_sum]
    simp only [p, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_coe, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_subtype s (fun _ ↦ Iff.rfl), mean, div_eq_mul_inv, mul_comm]
  let X : ↥s → ℝ := fun x ↦ f x - mean s f
  have hmeas : AEMeasurable X p.toMeasure := Measurable.of_discrete.aemeasurable
  have hbound : ∀ᵐ x ∂p.toMeasure, X x ∈ Set.Icc (-L) L :=
    Filter.Eventually.of_forall (fun x ↦ abs_le.mp (hf x x.2))
  have hzero : (∫ x, X x ∂p.toMeasure) = 0 := by
    change (∫ x : ↥s, (f x - mean s f) ∂p.toMeasure) = 0
    rw [integral_mean (fun x ↦ f x - mean s f), mean_sub, mean_const hs, sub_self]
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hmeas hbound hzero).mgf_le t
  change (∫ x : ↥s, Real.exp (t * (f x - mean s f)) ∂p.toMeasure) ≤ _ at h
  rw [integral_mean (fun x ↦ Real.exp (t * (f x - mean s f)))] at h
  have hwidth : (↑‖L - -L‖₊ : ℝ) / 2 = L := by
    change ‖L - -L‖ / 2 = L
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  simpa only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, hwidth] using h

/-- The centered moment generating function on the uniform slice is bounded
by that of a centered Gaussian with variance parameter `k * L²`. -/
theorem sliceMean_exp_centered_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (t : ℝ) :
    sliceMean s k (fun A ↦ Real.exp (t * (f A - sliceMean s k f))) ≤
      Real.exp ((k : ℝ) * L ^ 2 * t ^ 2 / 2) := by
  induction k generalizing s f with
  | zero => simp [sliceMean, mean, Finset.powersetCard_zero]
  | succ k ih =>
      let g : α → ℝ := fun x ↦ sliceMean (s.erase x) k (fun A ↦ f (insert x A))
      let m := sliceMean s (k + 1) f
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      have hm : m = mean s g := sliceMean_succ s k f
      have hg (x : α) (hx : x ∈ s) : |g x - mean s g| ≤ L :=
        abs_sub_mean_le hs hx (fun _ ha _ hb ↦ abs_sliceMean_insert_sub_le hk hf ha hb)
      let C := Real.exp ((k : ℝ) * L ^ 2 * t ^ 2 / 2)
      rw [sliceMean_succ]
      change mean s (fun x ↦ sliceMean (s.erase x) k
        (fun A ↦ Real.exp (t * (f (insert x A) - m)))) ≤ _
      calc
        _ = mean s (fun x ↦
            Real.exp (t * (g x - m)) * sliceMean (s.erase x) k
              (fun A ↦ Real.exp (t * (f (insert x A) - g x)))) := by
          apply mean_congr
          intro x _
          unfold sliceMean
          rw [← mean_const_mul]
          apply mean_congr
          intro A _
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ mean s (fun x ↦ C * Real.exp (t * (g x - m))) := by
          apply mean_mono
          intro x hx
          have hcard : k ≤ (s.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
          rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (ih hcard (hf.insert hx)) (Real.exp_nonneg _)
        _ = C * mean s (fun x ↦ Real.exp (t * (g x - mean s g))) := by
          rw [hm, mean_const_mul]
        _ ≤ C * Real.exp (L ^ 2 * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (mean_exp_centered_le hs hL hg t) (Real.exp_nonneg _)
        _ = _ := by
          dsimp only [C]
          rw [← Real.exp_add, Nat.cast_succ]
          congr 1
          ring

/-- The probability of an event for a uniformly chosen `k`-subset of `s`. -/
def sliceProbability (s : Finset α) (k : ℕ) (E : Finset α → Prop) : ℝ :=
  (((s.powersetCard k).filter E).card : ℝ) / (s.powersetCard k).card

omit [DecidableEq α] in
private theorem sliceProbability_le_one (s : Finset α) {k : ℕ} (hk : k ≤ s.card)
    (E : Finset α → Prop) : sliceProbability s k E ≤ 1 := by
  have hpos : 0 < ((s.powersetCard k).card : ℝ) := by
    exact_mod_cast (Finset.powersetCard_nonempty.mpr hk).card_pos
  rw [sliceProbability, div_le_one₀ hpos]
  exact_mod_cast Finset.card_filter_le _ _

private theorem sliceProbability_or_le (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤
      sliceProbability s k E + sliceProbability s k F := by
  let S := s.powersetCard k
  let events (P : Finset α → Prop) := S.filter P
  change ((events (fun A ↦ E A ∨ F A)).card : ℝ) / S.card ≤
    (events E).card / (S.card : ℝ) + (events F).card / (S.card : ℝ)
  rw [← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have mem_events (P : Finset α → Prop) (A : Finset α) :
      A ∈ events P ↔ A ∈ S ∧ P A := Finset.mem_filter
  have hsub : events (fun A ↦ E A ∨ F A) ⊆ events E ∪ events F := by
    intro A hA
    obtain ⟨hA, hE | hF⟩ := (mem_events (fun B ↦ E B ∨ F B) A).mp hA
    · exact Finset.mem_union_left _ ((mem_events E A).mpr ⟨hA, hE⟩)
    · exact Finset.mem_union_right _ ((mem_events F A).mpr ⟨hA, hF⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

omit [DecidableEq α] in
private theorem sliceProbability_mul_exp_le (s : Finset α) (k : ℕ)
    (X : Finset α → ℝ) (u t : ℝ) (ht : 0 ≤ t) :
    sliceProbability s k (fun A ↦ u ≤ X A) * Real.exp (t * u) ≤
      sliceMean s k (fun A ↦ Real.exp (t * X A)) := by
  rw [sliceProbability, sliceMean, mean, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ = ∑ _A ∈ (s.powersetCard k).filter (fun A ↦ u ≤ X A), Real.exp (t * u) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ A ∈ (s.powersetCard k).filter (fun A ↦ u ≤ X A), Real.exp (t * X A) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hA).2 ht)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ Real.exp_nonneg _)

/-- One-sided bounded differences for a uniform slice. -/
theorem sliceProbability_ge_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ f A - sliceMean s k f) ≤
      Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  let v := (k : ℝ) * L ^ 2
  have hden : 2 * (k : ℝ) * L ^ 2 = 2 * v := by dsimp [v]; ring
  rw [hden]
  by_cases hv : v = 0
  · simpa [hv] using sliceProbability_le_one s hk (fun A ↦ u ≤ f A - sliceMean s k f)
  have hvpos : 0 < v := lt_of_le_of_ne (by dsimp [v]; positivity) (Ne.symm hv)
  let t := u / v
  have ht : 0 ≤ t := div_nonneg hu hvpos.le
  have hmarkov := sliceProbability_mul_exp_le s k (fun A ↦ f A - sliceMean s k f) u t ht
  have hmgf := sliceMean_exp_centered_le hk hf hL t
  calc
    _ ≤ Real.exp (v * t ^ 2 / 2) / Real.exp (t * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (hmarkov.trans hmgf)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [t]
      field_simp [hv]
      ring

omit [DecidableEq α] in
private theorem sliceMean_neg (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    sliceMean s k (fun A ↦ -f A) = -sliceMean s k f := by
  simp [sliceMean, mean, Finset.sum_neg_distrib, neg_div]

/-- The lower tail has the same one-sided bound. -/
theorem sliceProbability_le_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ sliceMean s k f - f A) ≤
      Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  have hneg : ExchangeLipschitz s k (fun A ↦ -f A) L := by
    intro A hA B hB hAB
    change |-f A - -f B| ≤ L
    rw [show -f A - -f B = -(f A - f B) by ring, abs_neg]
    exact hf A hA B hB hAB
  simpa only [sliceMean_neg, neg_sub_neg] using sliceProbability_ge_le hk hneg hL hu

/-- The Green 39 exchange bounded-differences tail on the uniform slice. -/
theorem sliceProbability_abs_ge_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ |f A - sliceMean s k f|) ≤
      2 * Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  let m := sliceMean s k f
  have hE : (fun A : Finset α ↦ u ≤ |f A - m|) =
      (fun A ↦ u ≤ f A - m ∨ u ≤ m - f A) := by
    funext A
    exact propext (by rw [abs_eq_max_neg, le_max_iff, neg_sub])
  change sliceProbability s k (fun A ↦ u ≤ |f A - m|) ≤ _
  rw [hE]
  calc
    _ ≤ sliceProbability s k (fun A ↦ u ≤ f A - m) +
        sliceProbability s k (fun A ↦ u ≤ m - f A) := sliceProbability_or_le s k _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (sliceProbability_ge_le hk hf hL hu) (sliceProbability_le_le hk hf hL hu)

/-- If the variance parameter vanishes, the observable is constant on the slice. -/
theorem eq_sliceMean_of_variance_zero {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L)
    (hv : (k : ℝ) * L ^ 2 = 0) {A : Finset α} (hA : A ∈ s.powersetCard k) :
    f A = sliceMean s k f := by
  let m := sliceMean s k f
  let S := s.powersetCard k
  let d : ℝ := S.card
  by_contra hne
  have hd : 0 < d := by
    change 0 < (S.card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr ⟨A, hA⟩ : 0 < S.card)
  have hne' : f A - m ≠ 0 := sub_ne_zero.mpr hne
  let t := d / (f A - m)
  have ht : t * (f A - m) = d := div_mul_cancel₀ _ hne'
  have hmgf := sliceMean_exp_centered_le hk hf hL t
  rw [hv, zero_mul, zero_div, Real.exp_zero] at hmgf
  change (∑ B ∈ S, Real.exp (t * (f B - m))) / d ≤ 1 at hmgf
  have hsum : (∑ B ∈ S, Real.exp (t * (f B - m))) ≤ d := by
    simpa only [one_mul] using (div_le_iff₀ hd).mp hmgf
  have hpoint : Real.exp (t * (f A - m)) ≤ ∑ B ∈ S, Real.exp (t * (f B - m)) :=
    Finset.single_le_sum (fun B _ ↦ Real.exp_nonneg (t * (f B - m))) hA
  rw [ht] at hpoint
  linarith [Real.add_one_le_exp d, hpoint.trans hsum]

end

end Green39.Concentration

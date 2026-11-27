import SmoothConvolution
import SplitEvents

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {G ι : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Pointwise excess of the first-half convolution, translated by v. -/
def excess (μ : G → ℝ) (A : Finset G) (c : ℝ) (v z : G) :=
  max (conv (fun x ↦ μ (-x)) A (z-v) - c) 0

def l1Tail (n : ℕ) (u : ℝ) := Real.exp (-u^2 / (2*(n:ℝ)*2^2))

theorem l1_tail (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {a : ℕ} (ha : a ≤ Fintype.card G) {m D u : ℝ} (hb : ∀ x, μ x ≤ m)
    (hu : 0 ≤ u) (hD : Real.sqrt ((Fintype.card G : ℝ)*a*m) + u ≤ D) :
    sliceProbability Finset.univ a (fun A ↦ D < l1 μ a A) ≤ l1Tail a u := by
  have hE := sm_l1 μ hn hm ha
  have hcap := law_sum_sq_le_cap μ hn hm hb
  have hupper := hE.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcap
    (by positivity : 0 ≤ (Fintype.card G : ℝ)*a)))
  apply (prob_mono (s := Finset.univ) (F := fun A ↦ u ≤ l1 μ a A - sliceMean Finset.univ a (l1 μ a))
    (E := fun A ↦ D < l1 μ a A) (fun A _ h ↦ by linarith)).trans
  exact sliceProbability_ge_le (by simpa using ha) (l1_exchange μ hn hm _ a) (by norm_num) hu

theorem conv_max_tail (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {a : ℕ} (ha : a ≤ Fintype.card G) {m : ℝ} (hm0 : 0 < m) (hb : ∀ x, μ x ≤ m) (t : ℝ) :
    sliceProbability Finset.univ a (fun A ↦ ∃ z, t < conv μ A z) ≤
      (Fintype.card G : ℝ)*Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) := by
  let E (z : G) (A : Finset G) := t < conv μ A z
  have hz (z : G) : sliceProbability Finset.univ a (E z) ≤
      Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) := by
    have h := weight_tail (s := Finset.univ) (by simpa using ha) (fun x ↦ μ (z-x)) hm0
      (fun x _ ↦ ⟨hn _, hb _⟩) t
    have he : ∑ x, μ (z-x) = 1 := ((Equiv.subLeft z).sum_comp μ).trans hm
    apply (prob_mono (F := fun A ↦ t ≤ conv μ A z) (fun _ _ ha ↦ le_of_lt ha)).trans
    simpa only [conv, he, Finset.card_univ, mul_one] using h
  calc
    _ ≤ ∑ z, sliceProbability Finset.univ a (E z) := by
      simpa only [Finset.mem_univ, true_and] using prob_union Finset.univ a Finset.univ E
    _ ≤ _ := (Finset.sum_le_sum (fun z _ ↦ hz z)).trans_eq (by simp [nsmul_eq_mul])

theorem excess_tail (μ : G → ℝ) {a b : ℕ} (hab : a+b ≤ Fintype.card G)
    {A : Finset G} (hA : A.card = a) {c t D T : ℝ} (ht : 0 < t)
    (hc : (a:ℝ)/Fintype.card G ≤ c)
    (hD : l1 (fun x ↦ μ (-x)) a A ≤ D)
    (hcap : ∀ z, conv (fun x ↦ μ (-x)) A z ≤ t) :
    sliceProbability (Finset.univ \ A) b (fun B ↦ ∃ v, T < ∑ z ∈ B, excess μ A c v z) ≤
      (Fintype.card G:ℝ)*Real.exp (((Real.exp 1-1)*
        ((b:ℝ)/(Fintype.card G-a : ℕ)*D)-T)/t) := by
  let S := Finset.univ \ A
  have hN : S.card = Fintype.card G-a := by
    simp [S, Finset.card_sdiff_of_subset (Finset.subset_univ A), hA]
  have hb : b ≤ S.card := by rw [hN]; omega
  have hc0 : 0 ≤ c := (by positivity : 0 ≤ (a:ℝ)/Fintype.card G).trans hc
  have he0 (v z : G) : 0 ≤ excess μ A c v z := le_max_right _ _
  have het (v z : G) : excess μ A c v z ≤ t := max_le (by linarith [hcap (z-v)]) ht.le
  have hmass (v : G) : ∑ z ∈ S, excess μ A c v z ≤ D := by
    calc
      _ ≤ ∑ z, excess μ A c v z := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun z _ _ ↦ he0 _ z)
      _ ≤ ∑ z, |conv (fun x ↦ μ (-x)) A (z-v) - (a:ℝ)/Fintype.card G| := by
        apply Finset.sum_le_sum
        intro z _
        apply max_le _ (abs_nonneg _)
        exact (sub_le_sub_left hc _).trans (le_abs_self _)
      _ = l1 (fun x ↦ μ (-x)) a A := (Equiv.subRight v).sum_comp
        (fun z ↦ |conv (fun x ↦ μ (-x)) A z - (a:ℝ)/Fintype.card G|)
      _ ≤ _ := hD
  let E (v : G) (B : Finset G) := T < ∑ z ∈ B, excess μ A c v z
  have he (v : G) : sliceProbability S b (E v) ≤ Real.exp (((Real.exp 1-1)*
        ((b:ℝ)/(Fintype.card G-a : ℕ)*D)-T)/t) := by
    apply (prob_mono (F := fun B ↦ T ≤ ∑ z ∈ B, excess μ A c v z)
      (fun _ _ h ↦ le_of_lt h)).trans
    apply (weight_tail hb _ ht (fun z _ ↦ ⟨he0 v z, het v z⟩) T).trans
    rw [hN, Real.exp_le_exp]
    gcongr
    · exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    · exact hmass v
  calc
    _ ≤ ∑ v, sliceProbability S b (E v) := by
      simpa only [Finset.mem_univ, true_and] using prob_union S b Finset.univ E
    _ ≤ _ := (Finset.sum_le_sum (fun v _ ↦ he v)).trans_eq (by simp [nsmul_eq_mul])

/-- Finite failure bound for both inequalities of (4), simultaneously over a deterministic
family and all shifts. The two slices are sampled disjointly, and may have unequal sizes. -/
theorem equation_four (I : Finset ι) (μ : ι → G → ℝ) {m : ℝ} (hm : 0 < m)
    (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hmass : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hcap : ∀ i ∈ I, ∀ x, μ i x ≤ m)
    {a b : ℕ} (hab : a+b ≤ Fintype.card G) {c t D T u v : ℝ}
    (hc : (a:ℝ)/Fintype.card G ≤ c) (ht : 0 < t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (haD : Real.sqrt ((Fintype.card G:ℝ)*a*m) + u ≤ D)
    (hbD : Real.sqrt ((Fintype.card G:ℝ)*b*m) + v ≤ D) :
    splitProb Finset.univ a b (fun A B ↦ ∃ i ∈ I,
      D < l1 (μ i) b B ∨ ∃ shift, T < ∑ z ∈ B, excess (μ i) A c shift z) ≤
      (I.card:ℝ) * (l1Tail b v + l1Tail a u +
        (Fintype.card G:ℝ) * Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) +
        (Fintype.card G:ℝ) * Real.exp (((Real.exp 1-1)*((b:ℝ)/(Fintype.card G-a:ℕ)*D)-T)/t)) := by
  apply (split_union _ _ _ I _).trans
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro i hi
  let ν (x : G) := μ i (-x)
  have hν : ∑ x, ν x = 1 := (Equiv.sum_comp (Equiv.neg G) (μ i)).trans (hmass i hi)
  have hνn (x : G) : 0 ≤ ν x := hn i hi _
  have hνb (x : G) : ν x ≤ m := hcap i hi _
  let EA (A : Finset G) := D < l1 ν a A ∨ ∃ z, t < conv ν A z
  have hA := prob_or Finset.univ a (fun A ↦ D < l1 ν a A) (fun A ↦ ∃ z, t < conv ν A z)
  have hA' := hA.trans (add_le_add (l1_tail ν hνn hν (by omega) hνb hu haD)
    (conv_max_tail ν hνn hν (by omega) hm hνb t))
  have hB := l1_tail (μ i) (hn i hi) (hmass i hi) (by omega) (hcap i hi) hv hbD
  apply (split_bad_le (by simpa using hab) EA (fun B ↦ D < l1 (μ i) b B)
    (fun A B ↦ ∃ shift, T < ∑ z ∈ B, excess (μ i) A c shift z)
    (q := (Fintype.card G:ℝ)*Real.exp (((Real.exp 1-1)*((b:ℝ)/(Fintype.card G-a:ℕ)*D)-T)/t))
    (by positivity) ?_).trans
  · dsimp only [EA]
    linarith only [hA', hB]
  · intro A hA he
    change ¬(_ ∨ _) at he
    obtain ⟨h₁,h₂⟩ := not_or.mp he
    exact excess_tail _ hab (Finset.mem_powersetCard.mp hA).2 ht hc (le_of_not_gt h₁)
      (fun z ↦ le_of_not_gt (fun hz ↦ h₂ ⟨z,hz⟩))

end
end Green39.Smooth

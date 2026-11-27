import Assembly
import Fourier

noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory
open scoped Topology

def phase (t x : ℝ) : ℂ := Complex.exp ((t*x:ℝ)*Complex.I)
lemma norm_phase (t x : ℝ) : ‖phase t x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
lemma phase_add (t x y : ℝ) : phase t (x+y) = phase t x * phase t y := by
  simp [phase,mul_add,add_mul,Complex.exp_add]

lemma grid_transform {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    (S : ∀ i, Finset (V i)) (w : ∀ i, V i → ℝ) (v : ∀ i, V i → ℝ) (t : ℝ) :
    (∑ y ∈ Fintype.piFinset S, ((∏ i, w i (y i):ℝ):ℂ) * phase t (∑ i, v i (y i))) =
    ∏ i, ∑ a ∈ S i, (w i a:ℂ) * phase t (v i a) := by
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro y _
  rw [prod_mul_distrib,Complex.ofReal_prod]
  congr 1
  simp only [phase,mul_sum,Complex.ofReal_sum,sum_mul,Complex.exp_sum]

private lemma mass_pos {S : Finset ℕ} (hn : S.Nonempty) (hpr : ∀ p ∈ S, Nat.Prime p) : 0 < mass S :=
  sum_pos (fun p hp => inv_pos.mpr (by exact_mod_cast (hpr p hp).pos)) hn

private lemma success_transform (A : Finset ℕ) (hpr : ∀ p ∈ A, Nat.Prime p) (j : ℕ) (t : ℝ) :
    ‖∑ a ∈ success A, ((harmonic A a:ℝ):ℂ)*phase t (logN a)‖ =
      (∑ a ∈ success A, harmonic A a) * ‖char A j t‖ := by
  have prime_mem' (p : ℕ) (hp : p ∈ A) : p ∈ Integers A :=
    Nat.mem_factoredNumbers'.mpr fun q hq hqp => (Nat.prime_dvd_prime_iff_eq hq (hpr p hp)).mp hqp ▸ hp
  have h1 := sum_subtype_of_mem (s := A) (fun p : ℕ =>
    ((((p:ℝ)⁻¹/P A:ℝ):ℂ)*phase t (log p))) prime_mem'
  have h2 := sum_subtype_of_mem (s := A) (fun p : ℕ => (p:ℝ)⁻¹/P A) prime_mem'
  change ‖∑ a ∈ A.subtype (· ∈ Integers A), ((((a.val:ℝ)⁻¹/P A:ℝ):ℂ)*phase t (log a.val))‖ =
    (∑ a ∈ A.subtype (· ∈ Integers A), (a.val:ℝ)⁻¹/P A)*_
  rw [h1,h2,← sum_div]
  by_cases h : A.Nonempty
  · have hm := mass_pos h hpr
    have he : (∑ p ∈ A, ((((p:ℝ)⁻¹/P A:ℝ):ℂ)*phase t (log p))) =
        ((mass A/P A:ℝ):ℂ)*char A j t * phase t j := by
      unfold char
      have hn := Complex.ofReal_ne_zero.mpr hm.ne'
      simp only [Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_natCast]
      rw [show ∀ z : ℂ, ((mass A:ℂ)/(P A:ℂ))*(z/(mass A:ℂ)) = z/(P A:ℂ) from
        fun z => by field_simp [hn,Complex.ofReal_ne_zero.mpr (P_pos A).ne']]
      rw [sum_div,sum_mul]
      apply sum_congr rfl
      intro p hp
      change _ = ((p:ℂ)⁻¹ * phase t (log p-j) / (P A:ℂ)) * phase t j
      have hphase : phase t (log p) = phase t (log p-j)*phase t j := by rw [← phase_add]; congr 1; ring
      rw [hphase]; ring
    rw [he,norm_mul,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hm (P_pos A))]
    rfl
  · simp [not_nonempty_iff_eq_empty.mp h]

def rect (J : Finset ℕ) (A : J → Finset ℕ) (I : Finset J) (x : ∀ j, Integers (A j)) (j : J) :=
  if j ∈ I then success (A j) else {x j}

theorem rect_transform (J : Finset ℕ) (A : J → Finset ℕ) (I : Finset J)
    (hpr : ∀ i p, p ∈ A i → Nat.Prime p) (x : ∀ j, Integers (A j)) (t : ℝ) :
    let R := rect J A I x
    let W (y : ∀ j, Integers (A j)) := ∏ j, harmonic (A j) (y j)
    let Z (y : ∀ j, Integers (A j)) := ∑ j, logN (y j)
    ‖∑ y ∈ Fintype.piFinset R, (W y:ℂ) * phase t (Z y)‖ =
      (∑ y ∈ Fintype.piFinset R, W y) * ‖∏ i ∈ I, char (A i) i t‖ := by
  intro R W Z
  rw [grid_transform R (fun i => harmonic (A i)) (fun _ a => logN a), norm_prod,
    ← prod_univ_sum R (fun i => harmonic (A i)), norm_prod]
  calc
    _ = ∏ i, ((∑ a ∈ R i, harmonic (A i) a) * (if i ∈ I then ‖char (A i) i t‖ else 1)) := by
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ I
      · simpa only [R,rect,if_pos hi] using success_transform (A i) (hpr i) i t
      · simp [R,rect,hi,norm_phase,Real.norm_eq_abs,abs_of_nonneg (hnonneg (x i))]
    _ = _ := by rw [prod_mul_distrib]; simp [show J.attach ∩ I = I from inter_eq_right.mpr (fun i _ => mem_attach ..)]

theorem rect_support {Y : ℕ} (J : Finset ℕ) (A : J → Finset ℕ) (I : Finset J)
    (hA : ∀ i, A i ⊆ cell Y i) (x : ∀ j, Integers (A j)) :
    ∃ a : ℝ, ∀ y ∈ Fintype.piFinset (rect J A I x),
      a ≤ ∑ i, logN (y i) ∧ ∑ i, logN (y i) ≤ a+I.card := by
  let b (i : J) : ℝ := if i ∈ I then i.val else logN (x i)
  refine ⟨∑ i, b i,?_⟩
  intro y hy
  have hh (i : J) : b i ≤ logN (y i) ∧ logN (y i) ≤ b i + (if i ∈ I then 1 else 0) := by
    have h := Fintype.mem_piFinset.mp hy i
    by_cases hi : i ∈ I
    · simp only [rect,if_pos hi,success,mem_subtype] at h
      have hc := (mem_filter.mp (hA i h)).2
      simpa [b,hi] using And.intro hc.1 hc.2.le
    · simp only [rect,if_neg hi,mem_singleton] at h
      simp [b,hi,h]
  refine ⟨sum_le_sum (fun i _ => (hh i).1),?_⟩
  simpa [sum_add_distrib,← sum_filter,show J.attach ∩ I = I from inter_eq_right.mpr (fun i _ => mem_attach ..)] using sum_le_sum (s := univ) (fun i _ => (hh i).2)

#print axioms rect_transform
#print axioms rect_support
end Shift490

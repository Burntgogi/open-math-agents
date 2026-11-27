import Mathlib

/-! # Finite multiplicative-weights fitting for cyclic translate covers

The potential is cross entropy. Omitting the entropy of the fixed target
does not change the decrement, and permits zero target weights.
-/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι : Type*} [Fintype ι]

def testMean (m f : ι → ℝ) : ℝ := ∑ x, m x * f x
def normalizer (m f : ι → ℝ) (t : ℝ) : ℝ := ∑ x, m x * exp (t * f x)
def tilt (m f : ι → ℝ) (t : ℝ) (x : ι) : ℝ :=
  m x * exp (t * f x) / normalizer m f t
def potential (ν m : ι → ℝ) : ℝ := -∑ x, ν x * log (m x)

variable [Nonempty ι]

theorem normalizer_pos {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) :
    0 < normalizer m f t := by
  exact sum_pos (fun i _ => mul_pos (hm i) (exp_pos _)) univ_nonempty

theorem tilt_pos {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) (x : ι) :
    0 < tilt m f t x :=
  div_pos (mul_pos (hm x) (exp_pos _)) (normalizer_pos hm f t)

theorem sum_tilt {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) :
    ∑ x, tilt m f t x = 1 := by
  simp only [tilt, ← sum_div]
  exact div_self (normalizer_pos hm f t).ne'

theorem log_normalizer_le {m f : ι → ℝ} (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) (hf : ∀ x, |f x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    log (normalizer m f t) ≤ t * testMean m f + t^2 := by
  have hb (x : ι) : exp (t*f x) ≤ 1 + t*f x + t^2 := by
    have hab : |t*f x| ≤ t := by
      rw [abs_mul,abs_of_nonneg ht]
      simpa using mul_le_mul_of_nonneg_left (hf x) ht
    have he := (abs_le.mp (abs_exp_sub_one_sub_id_le (hab.trans ht'))).2
    have hsq := sq_le_sq.mpr (show |t*f x| ≤ |t| by simpa [abs_of_nonneg ht] using hab)
    linarith
  have hbound : normalizer m f t ≤ 1 + t*testMean m f + t^2 := calc
    _ ≤ ∑ x, m x * (1+t*f x+t^2) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hb i) (hm i).le)
    _ = ∑ x, (m x + t*(m x*f x) + m x*t^2) := by
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by simp only [sum_add_distrib,←mul_sum,←sum_mul,hs,one_mul,testMean]
  linarith [log_le_sub_one_of_pos (normalizer_pos hm f t)]

theorem potential_tilt {m ν : ι → ℝ} (hm : ∀ x, 0 < m x) (hν : ∑ x, ν x = 1)
    (f : ι → ℝ) (t : ℝ) :
    potential ν (tilt m f t) = potential ν m - t*testMean ν f + log (normalizer m f t) := by
  have he (x : ι) : ν x * log (tilt m f t x) =
      ν x * log (m x) + t*(ν x * f x) - ν x * log (normalizer m f t) := by
    rw [tilt,log_div (mul_pos (hm x) (exp_pos _)).ne' (normalizer_pos hm f t).ne',
      log_mul (hm x).ne' (exp_pos _).ne',log_exp]
    ring
  simp only [potential,he,sum_sub_distrib,sum_add_distrib,←mul_sum,←sum_mul,hν,one_mul,testMean]
  ring

/-- A separating test decreases the fitting potential by at least η²/16. -/
theorem update_decrement {m ν f : ι → ℝ} (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) (hν : ∑ x, ν x = 1) (hf : ∀ x, |f x| ≤ 1)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hgap : η/2 ≤ testMean ν f - testMean m f) :
    potential ν (tilt m f (η/4)) ≤ potential ν m - η^2/16 := by
  rw [potential_tilt hm hν]
  have h := log_normalizer_le hm hs hf (t := η/4) (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hgap hη]

omit [Nonempty ι] in
theorem potential_nonneg {ν m : ι → ℝ} (hν : ∀ x, 0 ≤ ν x) (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) : 0 ≤ potential ν m := by
  apply neg_nonneg.mpr
  apply sum_nonpos
  intro x _
  have hle : m x ≤ 1 := hs ▸ single_le_sum (f := m) (fun i _ => (hm i).le) (mem_univ x)
  exact mul_nonpos_of_nonneg_of_nonpos (hν x) (log_nonpos (hm x).le hle)

omit [Nonempty ι] in
theorem uniform_potential {ν : ι → ℝ} (hν : ∑ x, ν x = 1) :
    potential ν (fun _ => (Fintype.card ι : ℝ)⁻¹) = log (Fintype.card ι : ℝ) := by
  simp [potential, ←sum_mul, hν]

/-- The trajectory depends only on the ordered instructions and the learning rate. -/
def trajectory (f : ℕ → ι → ℝ) (η : ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => (Fintype.card ι : ℝ)⁻¹
  | n+1 => tilt (trajectory f η n) (f n) (η/4)

theorem trajectory_law (f : ℕ → ι → ℝ) (η : ℝ) (n : ℕ) :
    (∀ i, 0 < trajectory f η n i) ∧ ∑ i, trajectory f η n i = 1 := by
  induction n with
  | zero =>
    have hpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    constructor
    · intro i
      exact inv_pos.mpr hpos
    · simp [trajectory,hpos.ne']
  | succ n ih =>
    exact ⟨tilt_pos ih.1 _ _, sum_tilt ih.1 _ _⟩

/-- Any sequence of valid separating instructions must stop by the stated bound.
The target may be supported on an arbitrary subset, and the tests may be adaptive. -/
theorem iterations_le {ν : ι → ℝ} (hν : ∀ x, 0 ≤ ν x) (hνs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1) (f : ℕ → ι → ℝ) (n : ℕ)
    (hf : ∀ j < n, ∀ x, |f j x| ≤ 1)
    (hg : ∀ j < n, η/2 ≤ testMean ν (f j) - testMean (trajectory f η j) (f j)) :
    (n : ℝ) ≤ 16 * log (Fintype.card ι : ℝ) / η^2 := by
  have htel (j : ℕ) (hj : j ≤ n) :
      potential ν (trajectory f η j) + j*(η^2/16) ≤ log (Fintype.card ι : ℝ) := by
    induction j with
    | zero => simp [trajectory,uniform_potential hνs]
    | succ j ih =>
      have hj' : j < n := by omega
      obtain ⟨hp,hs⟩ := trajectory_law f η j
      have hd := update_decrement hp hs hνs (hf j hj') hη.le hη' (hg j hj')
      have hprev := ih hj'.le
      simp only [trajectory,Nat.cast_succ]
      linarith
  obtain ⟨hp,hs⟩ := trajectory_law f η n
  have h := potential_nonneg hν hp hs
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  linarith [htel n le_rfl]

#print axioms update_decrement
#print axioms iterations_le

end
end Green39.Fitting

import Selection
import Fluctuations
import Mathlib.Probability.ProbabilityMassFunction.Basic

noncomputable section
namespace Shift490
open Filter Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

def harmonicPMF (S : Finset ℕ) : PMF (Integers S) :=
  ⟨fun a => ENNReal.ofReal (harmonic S a), by
    have h := ENNReal.summable (f := fun a : Integers S => ENNReal.ofReal (harmonic S a))
    convert h.hasSum using 1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => hnonneg a) (harmonic_probability S).summable,
      (harmonic_probability S).tsum_eq, ENNReal.ofReal_one]⟩

def law (S : Finset ℕ) := (harmonicPMF S).toMeasure

instance (S : Finset ℕ) : IsProbabilityMeasure (law S) := PMF.toMeasure.isProbabilityMeasure _

lemma law_atom (S : Finset ℕ) (a : Integers S) : law S {a} = ENNReal.ofReal (harmonic S a) :=
  PMF.toMeasure_apply_singleton _ a (measurableSet_singleton _)

private lemma prime_mem {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (h : p ∈ S) : p ∈ Integers S := by
  refine Nat.mem_factoredNumbers'.mpr fun q hq hqp => ?_
  rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp hqp]

def success (S : Finset ℕ) := S.subtype (· ∈ Integers S)

lemma success_mass (S : Finset ℕ) (hpr : ∀ p ∈ S, Nat.Prime p) :
    (law S).real (success S) = mass S / P S := by
  classical
  have h := PMF.toMeasure_apply_finset (harmonicPMF S) (success S)
  rw [measureReal_def,law,h,ENNReal.toReal_sum (fun a _ => (harmonicPMF S).apply_ne_top a)]
  change (∑ a ∈ success S, (ENNReal.ofReal (harmonic S a)).toReal) = _
  have he (a : Integers S) : (ENNReal.ofReal (harmonic S a)).toReal = harmonic S a := ENNReal.toReal_ofReal (hnonneg a)
  simp only [he]
  simp only [harmonic,← sum_div]
  congr 1
  exact sum_subtype_of_mem (s := S) (fun p : ℕ => (p:ℝ)⁻¹) fun p hp => prime_mem (hpr p hp) hp

lemma success_lower (S : Finset ℕ) (hpr : ∀ p ∈ S, Nat.Prime p) (hs : mass S ≤ 1/2) :
    mass S/2 ≤ (law S).real (success S) := by
  rw [success_mass S hpr, div_eq_mul_inv (mass S) (P S), P, filter_eq_self.mpr hpr,
    prod_inv_distrib, inv_inv, mul_comm (mass S)]
  apply success_probability_lower S _ _ hs
  intro p hp
  have hh : 1 ≤ (p:ℝ) := by exact_mod_cast (hpr p hp).one_le
  exact ⟨by positivity,(inv_le_one₀ (by positivity)).mpr hh⟩

/-- Restriction to multiplicity one gives precisely the stated conditional lone-prime law. -/
theorem conditional_prime {S : Finset ℕ} (hpr : ∀ p ∈ S, Nat.Prime p) {p : ℕ} (hp : p ∈ S) :
    (law S).real {⟨p,prime_mem (hpr p hp) hp⟩} / (law S).real (success S) =
      (p:ℝ)⁻¹ / mass S := by
  rw [measureReal_def, law_atom, ENNReal.toReal_ofReal (hnonneg _),success_mass S hpr]
  unfold harmonic
  field_simp [ (P_pos S).ne' ]

set_option maxHeartbeats 1000000 in
/-- Full product-space fluctuation bound with no independence or variance hypotheses. -/
theorem independent_bins {ι : Type*} [Fintype ι] (A : ι → Finset ℕ)
    (hpr : ∀ i p, p ∈ A i → Nat.Prime p) (hsmall : ∀ i, mass (A i) ≤ 1/2)
    {m : ℝ} (hm : 0 < m) (hbudget : 8*m ≤ ∑ i, mass (A i)) :
    let μ := Measure.pi (fun i => law (A i))
    μ {ω | (∑ i, if ω i ∈ success (A i) then (1:ℝ) else 0) < m} ≤ ENNReal.ofReal (1/m) := by
  classical
  let μ := Measure.pi (fun i => law (A i))
  let X (i : ι) (v : Integers (A i)) : ℝ := if v ∈ success (A i) then 1 else 0
  have hmeas (i) : Measurable (X i) := measurable_of_countable _
  have hL (i) : MemLp (X i) 2 (law (A i)) :=
    (memLp_const (1:ℝ)).mono' (hmeas i).aestronglyMeasurable (ae_of_all _ fun v => by
      dsimp [X]; split <;> norm_num)
  have hE (i) : ∫ ω, X i (ω i) ∂μ = (law (A i)).real (success (A i)) := by
    have hmp := measurePreserving_eval (fun i => law (A i)) i
    have hmap := integral_map (μ := Measure.pi fun i => law (A i)) hmp.measurable.aemeasurable (hmeas i).aestronglyMeasurable
    rw [hmp.map_eq] at hmap
    change (∫ ω, X i (Function.eval i ω) ∂Measure.pi (fun i => law (A i))) = _
    rw [← hmap]
    have he : X i = ((success (A i)) : Set (Integers (A i))).indicator (fun _ => (1:ℝ)) := by
      funext v; by_cases hv : v ∈ success (A i) <;> simp [X,Set.indicator,hv]
    rw [he]
    rw [integral_indicator (Finset.measurableSet _), setIntegral_const, smul_eq_mul,mul_one]
  refine few_successes (μ := Measure.pi (fun i => law (A i))) univ (fun i ω => X i (ω i)) ?_ ?_ ?_ hm ?_
  · exact fun i _ => (hL i).comp_measurePreserving (measurePreserving_eval _ i)
  · intro i _ ω
    dsimp [X]; split <;> simp
  · intro i _ j _ hij
    exact (iIndepFun_pi fun i => (hmeas i).aemeasurable).indepFun hij
  · change 4*m ≤ ∑ i, ∫ ω, X i (ω i) ∂μ
    simp_rw [hE]
    have hh := sum_le_sum (s := (univ : Finset ι)) (fun i _ => success_lower (A i) (hpr i) (hsmall i))
    rw [← sum_div] at hh
    linarith

/-- On rectangular conditioning events all the coordinates remain independent. Choosing
each selected coordinate's event to be success preserves its conditional prime weights. -/
theorem restrict_cell_product {ι : Type*} [Fintype ι] (A : ι → Finset ℕ)
    (E : ∀ i, Set (Integers (A i))) :
    (Measure.pi fun i => law (A i)).restrict (Set.univ.pi E) =
    Measure.pi fun i => (law (A i)).restrict (E i) :=
  Measure.restrict_pi_pi _ _

#print axioms independent_bins
#print axioms conditional_prime
#print axioms restrict_cell_product
end Shift490

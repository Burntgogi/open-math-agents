import OldBadMass
import PrimeLabelMass
import PrimeCells
import LabelSum

/-! Transport of old squarefree harmonic mass to the finite sum of
continuous cell laws. The old integer 1 uses the empty label list. -/
namespace Erdos490Transfer
open Finset Filter Real MeasureTheory Erdos490PrimeCells
open scoped Topology ENNReal
noncomputable section
open Classical

def oldLabel (b : ℝ) (p : ℕ) : Label :=
  if h : p.Prime then ⟨boundary b p,boundary b (p+1),exp_pos _,by
    rw [boundary_succ b h]
    exact lt_mul_of_one_lt_right (exp_pos _) (one_lt_exp_iff.mpr (by exact inv_pos.mpr (by exact_mod_cast h.pos)))⟩
  else ⟨1,2,by norm_num,by norm_num⟩

lemma factor_in_cell (i : Label) :
    ∀ᵐ v ∂(limitFactor i : Measure ℝ), v ∈ Set.Ioc i.lo i.hi := by
  unfold limitFactor
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cellLaw_nonzero i.positive i.nonempty)]
  apply Measure.ae_smul_measure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

def law (b : ℝ) (s : List ℕ) := labelSum limitFactor (s.map (oldLabel b))

lemma law_displacement (b : ℝ) (s : List ℕ) (e : ℕ → ℝ)
    (he : ∀ p ∈ s, ∀ v ∈ Set.Ioc (oldLabel b p).lo (oldLabel b p).hi, |v-log p| ≤ e p) :
    ∀ᵐ v ∂(law b s : Measure ℝ),
      |v-(s.map (fun p : ℕ => log (p:ℝ))).sum| ≤ (s.map e).sum := by
  induction s with
  | nil =>
    change ∀ᵐ v ∂Measure.dirac (0:ℝ), |v-0| ≤ 0
    simp
  | cons p s ih =>
    let μ := law b s
    let ν := limitFactor (oldLabel b p)
    have ht := ih (fun q h => he q (List.mem_cons_of_mem _ h))
    have hh := (factor_in_cell (oldLabel b p)).mono (fun v h => he p (List.mem_cons_self) v h)
    change ∀ᵐ v ∂(sumLaw μ ν : Measure ℝ), |v-(_+_)| ≤ _+_
    let center := log (p:ℝ)+(s.map (fun q : ℕ => log (q:ℝ))).sum
    let radius := e p+(s.map e).sum
    let f (z : ℝ × ℝ) := z.1+z.2
    have hf : Measurable f := measurable_fst.add measurable_snd
    rw [sumLaw,ProbabilityMeasure.toMeasure_map,ProbabilityMeasure.toMeasure_prod]
    change ∀ᵐ v ∂Measure.map f ((μ:Measure ℝ).prod ν), |v-center| ≤ radius
    apply (ae_map_iff (p:=fun v => |v-center| ≤ radius) hf.aemeasurable (measurableSet_le (measurable_id.sub measurable_const).abs measurable_const)).mpr
    apply (Measure.ae_prod_iff_ae_ae (p:=fun z => |f z-center| ≤ radius) (measurableSet_le (hf.sub measurable_const).abs measurable_const)).mpr
    filter_upwards [ht] with a ha
    filter_upwards [hh] with d hd
    change |a+d-center| ≤ radius
    dsimp only [center,radius]
    rw [abs_le] at ha hd ⊢
    constructor <;> linarith [ha.1,ha.2,hd.1,hd.2]

def stripProbability (b : ℝ) (S : Finset ℕ) (l r : ℝ) :=
  (law b S.toList : Measure ℝ).real (Set.Ioc l r)

def transportedMass (b : ℝ) (C : Finset ℕ) (l r : ℝ) :=
  ∑ S ∈ C.powerset, (((∏ p ∈ S, p:ℕ):ℝ)⁻¹ * stripProbability b S l r)

private lemma full_strip {b δ l r : ℝ} (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    (e : ℕ → ℝ) (hc : ∀ p ∈ S, ∀ v ∈ Set.Ioc (oldLabel b p).lo (oldLabel b p).hi, |v-log p| ≤ e p)
    (hδ : ∑ p ∈ S, e p ≤ δ) (hl : l+δ < log (∏ p ∈ S, p:ℕ))
    (hr : log (∏ p ∈ S, p:ℕ) ≤ r-δ) : stripProbability b S l r = 1 := by
  have ha := law_displacement b S.toList e (fun p h => hc p (mem_toList.mp h))
  have hsum : (S.toList.map (fun p : ℕ => log (p:ℝ))).sum = log (∏ p ∈ S, p:ℕ) := by
    rw [Nat.cast_prod,log_prod (fun p h => by exact_mod_cast (hp p h).ne_zero)]
    simp
  have herr : (S.toList.map e).sum = ∑ p ∈ S, e p := by simp
  rw [hsum,herr] at ha
  have hall : ∀ᵐ v ∂(law b S.toList : Measure ℝ), v ∈ Set.Ioc l r := ha.mono fun v hv =>
    ⟨by linarith [(abs_le.mp hv).1],by linarith [(abs_le.mp hv).2]⟩
  have eq : Set.Ioc l r =ᵐ[(law b S.toList : Measure ℝ)] Set.univ := by
    filter_upwards [hall] with v hv; exact propext ⟨fun _ => Set.mem_univ v,fun _ => hv⟩
  unfold stripProbability Measure.real
  rw [measure_congr eq,measure_univ,ENNReal.toReal_one]

/-- Every good old integer in the contracted interval contributes its full
reciprocal mass to a distinct term in the enlarged transported strip. -/
theorem good_mass_transported (C : Finset ℕ) (hp : ∀ p ∈ C, p.Prime)
    (b l r δ : ℝ) (e : ℕ → ℝ)
    (hc : ∀ p ∈ C, ∀ v ∈ Set.Ioc (oldLabel b p).lo (oldLabel b p).hi, |v-log p| ≤ e p) :
    windowMass C (l+δ) (r-δ) - recMass (badWindow C (l+δ) (r-δ) δ e) ≤
      transportedMass b C l r := by
  let W := oldWindow C (l+δ) (r-δ)
  let B := badWindow C (l+δ) (r-δ) δ e
  let G := W \ B
  have sub : B ⊆ W := filter_subset .. 
  have good {m : ℕ} (hm : m ∈ G) :
      m.primeFactors ⊆ C ∧ Squarefree m ∧
      (∑ p ∈ m.primeFactors, e p) ≤ δ ∧ l+δ < log m ∧ log m ≤ r-δ := by
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hm
    obtain ⟨ha,hl,hr⟩ := mem_oldWindow.mp hw
    have hgood : ¬ ((∃ p ∈ C, p^2 ∣ m) ∨ δ ≤ ∑ p ∈ C with p ∣ m, e p) :=
      fun h => hn (mem_filter.mpr ⟨hw,h⟩)
    have hsub : m.primeFactors ⊆ C := fun p h => Nat.mem_factoredNumbers'.mp ha p
      (Nat.prime_of_mem_primeFactors h) (Nat.dvd_of_mem_primeFactors h)
    have eq : C.filter (· ∣ m) = m.primeFactors := by
      ext p
      simp only [mem_filter,Nat.mem_primeFactors]
      exact ⟨fun h => ⟨hp p h.1,h.2,ha.1⟩,fun h => ⟨hsub (Nat.mem_primeFactors.mpr h),h.2.1⟩⟩
    refine ⟨hsub,Nat.squarefree_iff_prime_squarefree.mpr (fun p hprime hdiv => ?_),?_,hl,hr⟩
    · have hd : p ∣ m := dvd_trans (dvd_mul_right p p) hdiv
      exact hgood (.inl ⟨p,Nat.mem_factoredNumbers'.mp ha p hprime hd,by simpa [pow_two] using hdiv⟩)
    · rw [← eq]; exact le_of_not_ge (fun h => hgood (.inr h))
  have hj : Set.InjOn Nat.primeFactors G := by
    intro m hm n hn he
    simpa [Nat.prod_primeFactors_of_squarefree (good hm).2.1,Nat.prod_primeFactors_of_squarefree (good hn).2.1]
      using congrArg (fun S : Finset ℕ => ∏ p ∈ S, p) he
  have heq : windowMass C (l+δ) (r-δ) - recMass B = recMass G := by
    exact sub_eq_iff_eq_add.mpr (sum_sdiff sub).symm
  rw [heq]
  let f (S : Finset ℕ) := (((∏ p ∈ S, p:ℕ):ℝ)⁻¹ * stripProbability b S l r)
  calc
    _ = ∑ S ∈ G.image Nat.primeFactors, f S := by
      rw [sum_image hj]
      apply sum_congr rfl
      intro m hm
      obtain ⟨hsub,hsq,hδ,hl,hr⟩ := good hm
      have he := Nat.prod_primeFactors_of_squarefree hsq
      have hstrip := full_strip m.primeFactors (fun p h => hp _ (hsub h)) e (fun p h => hc p (hsub h))
        hδ (he ▸ hl) (he ▸ hr)
      simp only [f,hstrip,he,mul_one]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun _ h => by
      obtain ⟨m,hm,rfl⟩ := mem_image.mp h
      exact mem_powerset.mpr (good hm).1) (fun _ _ _ => mul_nonneg (by positivity) measureReal_nonneg)

#print axioms good_mass_transported
end
end Erdos490Transfer

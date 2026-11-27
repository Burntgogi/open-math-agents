import Components

noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

def testAt (κ : Measure ℝ) (f : ℝ → ℝ) (s x : ℝ) := ∫ u, f (s-x-u) ∂κ

/-- One finite successful component, with the other coordinates frozen. The sums carry
unnormalized weights, so rectangular conditioning does not introduce divisions by zero. -/
def SuccessfulComponents (Y : ℕ) : Prop :=
  ∀ c H δ η : ℝ, 0 < c → 0 ≤ H → 0 < δ → 0 < η →
  ∃ (m : ℕ) (κ : Measure ℝ), 0 < m ∧ 1/(m:ℝ) ≤ η/2 ∧ IsProbabilityMeasure κ ∧
    (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧
  ∀ (J : Finset ℕ) (A : J → Finset ℕ), (∀ j, A j ⊆ cell Y j) →
    (∀ j, Bands (A j) j m c) →
  ∀ (I : Finset J), I.card = m →
  ∀ (x : ∀ j, Integers (A j)) (f : ℝ → ℝ), Measurable f → (∀ z, 0 ≤ f z ∧ f z ≤ 1) →
  ∀ s t : ℝ, |s| ≤ H → |t| ≤ H →
    let R := Fintype.piFinset (fun j => if j ∈ I then success (A j) else {x j})
    let W := fun y : ∀ j, Integers (A j) => ∏ j, harmonic (A j) (y j)
    let z := fun y : ∀ j, Integers (A j) => ∑ j, logN (y j)
    (∑ y ∈ R, W y * testAt κ f s (z y)) ≤ ∑ y ∈ R, W y * (testAt κ f t (z y) + η/2)

private lemma test01 {κ : Measure ℝ} [IsProbabilityMeasure κ] {f : ℝ → ℝ} (hf : Measurable f)
    (h01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (s x : ℝ) : 0 ≤ testAt κ f s x ∧ testAt κ f s x ≤ 1 := by
  refine ⟨integral_nonneg (fun _ => (h01 _).1),?_⟩
  have hh : Integrable (fun u => f (s-x-u)) κ :=
    (integrable_const (μ := κ) (1:ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun u => by change ‖f (s-x-u)‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (h01 _).1]; exact (h01 _).2)
  simpa [testAt] using integral_mono hh (integrable_const (μ := κ) (1:ℝ)) (fun u => (h01 _).2)

private lemma bounded_integrable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {v : Ω → ℝ} (h : ∀ x, 0 ≤ v x ∧ v x ≤ 1) : Integrable v μ :=
  (integrable_const (μ := μ) (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h x).1]; exact (h x).2)

theorem smoothing_of_successful {Y : ℕ} (h : SuccessfulComponents Y) : FiniteSmoothing Y := by
  classical
  intro c H δ η hc hH hδ hη
  obtain ⟨m,κ,hm,hfrac,hκ,hsupp,hcomp⟩ := h c H δ η hc hH hδ hη
  let _ := hκ
  refine ⟨m,hm,?_⟩
  intro J A hinc hbands hbudget
  let B (i : J) := A i
  let Ω := ∀ i : J, Integers (B i)
  let μ := Measure.pi (fun i => law (B i))
  let D := (univ : Finset J).biUnion B
  have hD : D = J.biUnion A := by ext p; simp [D,B]
  rw [← hD]
  have hpr (i : J) (p : ℕ) (hp : p ∈ B i) : Nat.Prime p :=
    (mem_filter.mp (mem_filter.mp (hinc _ i.property hp)).1).2
  have hd : Pairwise (fun i j : J => Disjoint (B i) (B j)) := by
    intro i j hij
    refine disjoint_left.mpr fun p hp hq => ?_
    have hi := (mem_filter.mp (hinc _ i.property hp)).2
    have hj := (mem_filter.mp (hinc _ j.property hq)).2
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Subtype.ext he)) with he | he
    · have hn : ((i.val+1:ℕ):ℝ) ≤ j.val := by exact_mod_cast he
      push_cast at hn; linarith [hi.2,hj.1]
    · have hn : ((j.val+1:ℕ):ℝ) ≤ i.val := by exact_mod_cast he
      push_cast at hn; linarith [hj.2,hi.1]
  let G (i : J) := success (B i)
  let bad : Set Ω := {x | (successes G x).card < m}
  have hbad : μ.real bad ≤ η/2 := by
    have hb := independent_bins B hpr (fun i => (hbands _ i.property).1) (m := (m:ℝ))
      (by exact_mod_cast hm) (by change 8*(m:ℝ) ≤ ∑ i ∈ J.attach, mass (A i.val); rw [sum_attach J (fun j => mass (A j))]; exact hbudget)
    have hset : bad = {x : Ω | (∑ i, if x i ∈ G i then (1:ℝ) else 0) < m} := by
      ext x
      simp only [bad,Set.mem_ofPred_eq,successes,← sum_filter, sum_const,nsmul_eq_mul,mul_one,Nat.cast_lt]
    rw [hset,measureReal_def]
    exact ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans (by rw [ENNReal.toReal_ofReal (by positivity)]; exact hfrac))
  refine ⟨κ,hκ,hsupp,?_⟩
  intro f hf h01 s t hs ht
  let Z (x : Ω) := ∑ j, logN (x j)
  let W (x : Ω) := ∏ j, harmonic (B j) (x j)
  let T (r : ℝ) (x : Ω) := testAt κ f r (Z x)
  have hatom (x : Ω) : μ.real {x} = W x := by
    change ((Measure.pi (fun i => law (B i))) {x}).toReal = ∏ i, harmonic (B i) (x i)
    rw [Measure.pi_singleton]
    simp only [law_atom,ENNReal.toReal_prod]
    exact prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (hnonneg (x i)))
  have bl (r : ℝ) : blend D κ f r = ∫ x, T r x ∂μ := by
    let v (a : Integers D) := testAt κ f r (logN a)
    have hv : Integrable v (law D) := bounded_integrable (fun x => test01 hf h01 r _)
    have hh : blend D κ f r = ∫ a, v a ∂law D := by
      rw [integral_countable hv]
      apply tsum_congr
      intro a
      simp only [measureReal_def,law_atom,ENNReal.toReal_ofReal (hnonneg a),smul_eq_mul]
      rfl
    rw [hh, ← product_law B hd, integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable v).aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    have he : logN (join B x) = Z x := by simp [join,Z,logN,Real.log_prod (fun i _ => (nat_pos (x i)).ne')]
    change testAt κ f r (logN (join B x)) = _
    rw [he]
  rw [bl,bl]
  have hT (r : ℝ) : Integrable (T r) μ := bounded_integrable (fun x => test01 hf h01 r _)
  let fail (x : Ω) := bad.indicator (fun _ => (1:ℝ)) x
  have hbadm : MeasurableSet bad := (Set.to_countable _).measurableSet
  have hfail : Integrable fail μ := (integrable_const (1:ℝ)).indicator hbadm
  let upper (x : Ω) := T t x + η/2 + fail x
  have hU : Integrable upper μ := ((hT t).add (integrable_const _)).add hfail
  have hb : (∫ x, T s x ∂μ) ≤ ∫ x, upper x ∂μ := by
    apply integrate_components μ (component G m) (self_mem_component G m) (fun _ _ => component_eq G m)
      (hT s) hU
    intro x
    have same (y : Ω) (hy : y ∈ component G m x) : successes G y = successes G x := component_successes G m hy
    by_cases hgood : m ≤ (successes G x).card
    · have hh := hcomp J B (fun i => hinc _ i.property) (fun i => (hbands _ i.property).2)
        (select m (successes G x)) (select_size hgood) x f hf h01 s t hs ht
      change ∑ y ∈ component G m x, W y*T s y ≤ ∑ y ∈ component G m x, W y*(T t y+η/2) at hh
      simp only [hatom]
      refine hh.trans (sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (by rw [← hatom]; positivity))
      have hh' : y ∉ bad := fun hy' => by
        change (successes G y).card < m at hy'
        rw [same y hy] at hy'; omega
      simp [upper,fail,hh']
    · apply sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hy' : y ∈ bad := by change (successes G y).card < m; rw [same y hy]; omega
      have h1 := (test01 (κ := κ) hf h01 s (Z y)).2
      have h2 := (test01 (κ := κ) hf h01 t (Z y)).1
      simp only [upper,fail,Set.indicator_of_mem hy',T]
      linarith
  have hI : (∫ x, fail x ∂μ) = μ.real bad := by
    change (∫ x, bad.indicator (fun _ => (1:ℝ)) x ∂μ) = _
    rw [integral_indicator hbadm,setIntegral_const,smul_eq_mul,mul_one]
  change (∫ x, T s x ∂μ) ≤ (∫ x, T t x ∂μ) + η
  dsimp only [upper] at hb
  rw [integral_add (show Integrable (fun x => T t x + η/2) μ from (hT t).add (integrable_const _)) hfail,
    integral_add (hT t) (integrable_const _),integral_const,probReal_univ,one_smul,hI] at hb
  linarith

#print axioms smoothing_of_successful
end Shift490

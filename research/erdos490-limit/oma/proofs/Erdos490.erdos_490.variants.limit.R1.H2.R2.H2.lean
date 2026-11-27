import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1_H2_R2
import Mathlib

/-! Bounded shifts on one fixed color, conditional on the effective θ bound. Adapted from the local Shift490 Fourier, prime-cell and selection proofs. -/

/- Arithmetic -/
section
noncomputable section
namespace Shift490
open Finset Filter
abbrev Integers := Nat.factoredNumbers

def P (S : Finset ℕ) : ℝ := ∏ p ∈ S with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹

theorem P_pos (S : Finset ℕ) : 0 < P S := by
  apply prod_pos
  intro p hp
  have h : 1 < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))

def reciprocal : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by simp [mul_comm]

theorem harmonic_sum (S : Finset ℕ) :
    HasSum (fun n : Integers S => ((n : ℕ) : ℝ)⁻¹) (P S) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocal) ?_ S).2
  intro p hp
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact (inv_lt_one₀ (by positivity)).mpr h

def harmonic (S : Finset ℕ) (n : Integers S) := ((n : ℕ) : ℝ)⁻¹ / P S

theorem harmonic_probability (S : Finset ℕ) : HasSum (harmonic S) 1 := by
  unfold harmonic
  simpa only [div_self (P_pos S).ne'] using (harmonic_sum S).div_const (P S)

abbrev logN {S : Finset ℕ} (n : Integers S) := Real.log (n : ℕ)
def atom {S : Finset ℕ} (w : ℝ) (n : Integers S) : ℝ :=
  if logN n ≤ w then Real.exp (-w) else 0
def F (S : Finset ℕ) (w : ℝ) : ℝ := ∑' n : Integers S, atom w n

lemma nat_pos {S} (n : Integers S) : 0 < ((n : ℕ) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero n.property.1

lemma atom_nonneg {S w} (n : Integers S) : 0 ≤ atom w n := by
  unfold atom
  split <;> positivity

lemma atom_le {S w} (n : Integers S) : atom w n ≤ ((n : ℕ) : ℝ)⁻¹ := by
  unfold atom logN
  split_ifs with h
  · rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (nat_pos n)]
    exact (Real.log_le_iff_le_exp (nat_pos n)).mp h
  · positivity

lemma summable_atom (S w) : Summable (@atom S w) :=
  Summable.of_nonneg_of_le atom_nonneg atom_le (harmonic_sum S).summable

def countSet (S : Finset ℕ) (w : ℝ) :=
  (range (⌊Real.exp w⌋₊ + 1)).filter (· ∈ Integers S)

theorem F_eq_card (S w) : F S w = Real.exp (-w) * (countSet S w).card := by
  classical
  let t := (countSet S w).subtype (· ∈ Integers S)
  have ht (n : Integers S) : n ∈ t ↔ logN n ≤ w := by
    simp [t, countSet, logN, Nat.le_floor_iff (Real.exp_pos w).le,
      Real.log_le_iff_le_exp (nat_pos n), n.property]
  rw [F, tsum_eq_sum (s := t) (fun n hn => by simp [atom, mt (ht n).mpr hn])]
  calc
    _ = ∑ _n ∈ t, Real.exp (-w) := sum_congr rfl fun n hn => if_pos ((ht n).mp hn)
    _ = _ := by
      have he : t.card = (countSet S w).card := by
        simp [t, Finset.card_subtype, Finset.filter_eq_self.mpr
          (show ∀ n ∈ countSet S w, n ∈ Integers S from fun n hn => (mem_filter.mp hn).2)]
      simp [he, mul_comm]

def multiply {A B : Finset ℕ} (x : Integers A × Integers B) : Integers (A ∪ B) :=
  ⟨x.1.val * x.2.val, Nat.mul_mem_factoredNumbers
    (Nat.factoredNumbers_mono subset_union_left x.1.property)
    (Nat.factoredNumbers_mono subset_union_right x.2.property)⟩

theorem multiply_bijective {A B : Finset ℕ} (hd : Disjoint A B) :
    Function.Bijective (@multiply A B) := by
  have cop (a : Integers A) (b : Integers B) : a.val.Coprime b.val :=
    Nat.coprime_of_dvd fun p hp ha hb => Finset.disjoint_left.mp hd
      (Nat.mem_factoredNumbers'.mp a.property p hp ha)
      (Nat.mem_factoredNumbers'.mp b.property p hp hb)
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have he : a.val * b.val = c.val * d.val := congrArg Subtype.val h
    have hac := (cop a d).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a.val b.val)
    have hca := (cop c b).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right c.val d.val)
    have h1 := Nat.dvd_antisymm hac hca
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero c.property.1) (h1 ▸ he)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro n
    let l := n.val.primeFactorsList
    have part := List.Perm.prod_eq (List.filter_append_perm (fun p => decide (p ∈ A)) l)
    rw [List.prod_append, Nat.prod_primeFactorsList n.property.1] at part
    have other : l.filter (fun x => !decide (x ∈ A)) = l.filter (· ∈ B) := by
      apply List.filter_congr
      intro p hp
      have := mem_union.mp (n.property.2 p hp)
      have hd' : p ∈ A → p ∉ B := fun ha => Finset.disjoint_left.mp hd ha
      grind
    rw [other] at part
    exact ⟨(⟨_, Nat.prod_mem_factoredNumbers A n.val⟩,
      ⟨_, Nat.prod_mem_factoredNumbers B n.val⟩), Subtype.ext part⟩

theorem normalized_convolution {A B : Finset ℕ} (hd : Disjoint A B) (w : ℝ) :
    F (A ∪ B) w = P A * ∑' a : Integers A, harmonic A a * F B (w - logN a) := by
  let e := Equiv.ofBijective _ (multiply_bijective hd)
  have hs : Summable (fun x => atom w (e x)) := (e.summable_iff).mpr (summable_atom (A ∪ B) w)
  rw [F, ← e.tsum_eq, hs.tsum_prod, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [← mul_assoc, harmonic, mul_comm (P A), div_mul_cancel₀ _ (P_pos A).ne', F, ← tsum_mul_left]
  apply tsum_congr
  intro b
  change (if Real.log ((a.val * b.val : ℕ) : ℝ) ≤ w then _ else _) = _
  simp only [Nat.cast_mul, Real.log_mul (nat_pos a).ne' (nat_pos b).ne', atom, logN]
  simp only [show Real.log (a : ℕ) + Real.log (b : ℕ) ≤ w ↔ Real.log (b : ℕ) ≤ w - Real.log (a : ℕ) by constructor <;> intro h <;> linarith]
  by_cases h : Real.log (b : ℕ) ≤ w - Real.log (a : ℕ)
  · simp only [if_pos h]
    rw [show -(w - Real.log (a : ℕ)) = Real.log (a : ℕ) + (-w) by ring, Real.exp_add,
      Real.exp_log (nat_pos a), ← mul_assoc, inv_mul_cancel₀ (nat_pos a).ne', one_mul]
  · simp [h]





end Shift490
end
end

/- Law -/
section
noncomputable section
namespace Shift490
open Finset Real Filter MeasureTheory
open scoped Topology

theorem P_union {D B : Finset ℕ} (hd : Disjoint D B) : P (D ∪ B) = P D * P B := by
  simp only [P,filter_union,prod_union (hd.mono (filter_subset Nat.Prime D) (filter_subset Nat.Prime B))]

theorem one_le_P (S : Finset ℕ) : 1 ≤ P S := by
  apply Finset.one_le_prod
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  apply (one_le_inv₀ (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))).mpr
  linarith [show 0 ≤ (p:ℝ)⁻¹ by positivity]

lemma hnonneg {D} (a : Integers D) : 0 ≤ harmonic D a :=
  div_nonneg (by positivity) (P_pos D).le

def avg (D : Finset ℕ) (f : ℝ → ℝ) := ∑' a : Integers D, harmonic D a * f (logN a)

lemma avg_summable {D : Finset ℕ} {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    Summable (fun a : Integers D => harmonic D a * f (logN a)) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (hnonneg a) (hf _).1)
    (fun a => mul_le_mul_of_nonneg_left (hf _).2 (hnonneg a))
    ((harmonic_probability D).summable.mul_right M)

lemma avg_mul (D) (c : ℝ) (f : ℝ → ℝ) :
    avg D (fun x => c * f x) = c * avg D f := by
  simp only [avg, ← tsum_mul_left, mul_left_comm c]

def rootReciprocal : ℕ →* ℝ where
  toFun n := (√(n:ℝ))⁻¹
  map_one' := by simp
  map_mul' := by simp [Real.sqrt_mul (Nat.cast_nonneg _), mul_comm]

theorem half_moment (D : Finset ℕ) :
    Summable (fun a : Integers D => harmonic D a * exp (logN a / 2)) := by
  have hp {p : ℕ} (h : p.Prime) : ‖rootReciprocal p‖ < 1 := by
    change ‖(√(p:ℝ))⁻¹‖ < 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have h' : 1 < (p:ℝ) := by exact_mod_cast h.one_lt
    have hs : 1 < √(p:ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ)]
    exact (inv_lt_one₀ (by positivity)).mpr hs
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := rootReciprocal) hp D).2.summable.div_const (P D)
  apply h.congr
  intro a
  change (√(a.val:ℝ))⁻¹ / P D = ((a.val:ℝ)⁻¹ / P D) * exp (log (a.val:ℝ) / 2)
  rw [Real.exp_half, Real.exp_log (nat_pos a)]
  field_simp [Real.sqrt_ne_zero'.mpr (nat_pos a), (nat_pos a).ne', (P_pos D).ne']
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg a.val)]

def moment (D : Finset ℕ) := ∑' a : Integers D, harmonic D a * exp (logN a / 2)

/-- Dual total-variation formulation for the translate of a smoothed probability law. -/
def blend (D : Finset ℕ) (κ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) :=
  avg D (fun v => ∫ u, f (t - v - u) ∂κ)

def KernelFlat (D : Finset ℕ) (H δ η : ℝ) : Prop :=
  ∃ κ : Measure ℝ, IsProbabilityMeasure κ ∧ (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧
    ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    ∀ t z : ℝ, |t| ≤ H → |z| ≤ H → blend D κ f t ≤ blend D κ f z + η

/-- Past and future translates of the same kernel sandwich a one-sided regular profile.
The kernel can be any probability on the stated interval. -/
theorem desmooth {D : Finset ℕ} {H δ η : ℝ} (flat : KernelFlat D H δ η)
    {f : ℝ → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hslow : ∀ x y, x ≤ y → f x ≤ exp (y-x) * f y)
    {s t : ℝ} (hs : |s+δ| ≤ H) (ht : |t| ≤ H) (hδ : 0 ≤ δ) :
    avg D (fun v => f (s-v)) ≤ avg D (fun v => f (t-v)) +
      (exp δ - 1)*2 + η := by
  obtain ⟨κ,hκ,hsupp,hflat⟩ := flat
  let _ := hκ
  let I (r v : ℝ) := ∫ u, f (r-v-u) ∂κ
  have hint (r v : ℝ) : Integrable (fun u => f (r-v-u)) κ := by
    apply (integrable_const (μ := κ) (1:ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
    exact ae_of_all _ fun u => by
      change ‖f (r-v-u)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (h01 _).1]
      exact (h01 _).2
  have hI (r v : ℝ) : 0 ≤ I r v ∧ I r v ≤ 1 :=
    ⟨integral_nonneg (fun _ => (h01 _).1), by
      simpa [I] using integral_mono (hint r v) (integrable_const (μ := κ) (1:ℝ)) (fun u => (h01 _).2)⟩
  have err : 0 ≤ exp δ - 1 := sub_nonneg.mpr (Real.one_le_exp hδ)
  have point (x y : ℝ) (hxy : x ≤ y) (hy : y-x ≤ δ) :
      f x ≤ f y + (exp δ - 1) := by
    have h' := (hslow x y hxy).trans (mul_le_mul_of_nonneg_right (exp_le_exp.mpr hy) (h01 y).1)
    nlinarith [mul_nonneg err (sub_nonneg.mpr (h01 y).2)]
  have past (v : ℝ) : f (s-v) ≤ I (s+δ) v + (exp δ-1) := by
    have h := integral_mono_ae (integrable_const (μ := κ) (f (s-v)))
      ((hint (s+δ) v).add (integrable_const (exp δ-1))) (by
        filter_upwards [hsupp] with u hu
        exact point _ _ (by linarith [hu.2]) (by linarith [hu.1]))
    simpa [I, integral_add (hint (s+δ) v) (integrable_const (exp δ-1))] using h
  have future (v : ℝ) : I t v ≤ f (t-v) + (exp δ-1) := by
    have h := integral_mono_ae (hint t v) (integrable_const (μ := κ) (f (t-v)+(exp δ-1))) (by
      filter_upwards [hsupp] with u hu
      exact point _ _ (by linarith [hu.1]) (by linarith [hu.2]))
    simpa [I] using h
  have lift {f g : ℝ → ℝ} (h1 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
      (h2 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (h : ∀ x, f x ≤ g x + (exp δ-1)) :
      avg D f ≤ avg D g + (exp δ-1) := by
    have hsum := (harmonic_probability D).mul_right (exp δ-1)
    have hb := (avg_summable (D := D) h2).hasSum.add hsum
    simpa [avg] using hasSum_le (fun a => by
      simpa [mul_add] using mul_le_mul_of_nonneg_left (h (logN a)) (hnonneg a))
      (avg_summable (D := D) h1).hasSum hb
  have h1 := lift (fun x => h01 (s-x)) (hI (s+δ)) past
  have h2 := lift (hI t) (fun x => h01 (t-x)) future
  have h3 := hflat f hf h01 (s+δ) t hs ht
  change avg D (I (s+δ)) ≤ avg D (I t) + η at h3
  linarith



end Shift490
end
end

/- Selection -/
section
noncomputable section
namespace Shift490
open Real Filter Finset
open scoped Topology

def primesAt (Y : ℕ) (x : ℝ) := (Finset.Icc Y ⌊x⌋₊).filter Nat.Prime
def side (Y : ℕ) (x : ℝ) (q : ℕ → Bool) (b : Bool) := (primesAt Y x).filter (fun p => q p = b)

def cell (Y j : ℕ) := (primesAt Y (exp (j+1))).filter
  (fun p : ℕ => (j:ℝ) ≤ log p ∧ log p < (j:ℝ)+1)

def mass (A : Finset ℕ) := ∑ p ∈ A, (p:ℝ)⁻¹

def char (A : Finset ℕ) (j : ℕ) (t : ℝ) : ℂ :=
  (∑ p ∈ A, ((p:ℂ)⁻¹ * Complex.exp ((t*(log p - j):ℝ) * Complex.I))) / (mass A:ℂ)

def Bands (A : Finset ℕ) (j m : ℕ) (c : ℝ) : Prop :=
  (∀ t : ℝ, |t| ≤ 1 → ‖char A j t‖ ≤ exp (-c*t^2)) ∧
  (∀ t : ℝ, 1 < |t| → |t| ≤ (m:ℝ)^2 → ‖char A j t‖ ≤ exp (-c))

/-- Only the following consequences of local PNT and compactness of dominated cell laws
are required. The threshold is allowed to depend on the frequency cutoff. -/
def PrimeCellInput (Y : ℕ) : Prop :=
  (∀ᶠ j : ℕ in atTop, 2/(3*(j:ℝ)) ≤ mass (cell Y j) ∧ mass (cell Y j) ≤ 1/2) ∧
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, ∀ A ⊆ cell Y j,
    1/(3*(j:ℝ)) ≤ mass A → Bands A j m c

/-- Finite analytic input. All colors and moving cutoffs have disappeared. Cells have
disjoint prime supports, normalized reciprocal prime laws, and a mean-success budget. -/
def FiniteSmoothing (Y : ℕ) : Prop :=
  ∀ c H δ η : ℝ, 0 < c → 0 ≤ H → 0 < δ → 0 < η → ∃ m : ℕ, 0 < m ∧
    ∀ (J : Finset ℕ) (A : ℕ → Finset ℕ), (∀ j ∈ J, A j ⊆ cell Y j) →
    (∀ j ∈ J, mass (A j) ≤ 1/2 ∧ Bands (A j) j m c) →
    8*(m:ℝ) ≤ ∑ j ∈ J, mass (A j) → KernelFlat (J.biUnion A) H δ η

private def bins (Y : ℕ) (q : ℕ → Bool) (b : Bool) (j : ℕ) :=
  (cell Y j).filter (fun p => q p = b)

private def goodWeight (Y : ℕ) (q : ℕ → Bool) (b : Bool) (j : ℕ) :=
  if 1/(3*(j:ℝ)) ≤ mass (bins Y q b j) then (j:ℝ)⁻¹ else 0

private theorem divergent_color {Y} (pnt : PrimeCellInput Y) (q : ℕ → Bool) :
    ∃ b, ¬ Summable (goodWeight Y q b) := by
  by_contra! h
  apply Real.not_summable_natCast_inv
  apply Summable.of_norm_bounded_eventually_nat ((h true).add (h false))
  filter_upwards [pnt.1, eventually_gt_atTop 0] with j hj hj0
  have hsplit : mass (bins Y q true j) + mass (bins Y q false j) = mass (cell Y j) := by
    unfold mass bins
    simpa using sum_filter_add_sum_filter_not (cell Y j) (fun p => q p = true) (fun p => (p:ℝ)⁻¹)
  simp only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (j:ℝ)⁻¹ by positivity),goodWeight]
  have hh : 2/(3*(j:ℝ)) = 1/(3*j)+1/(3*j) := by ring
  have hn : 0 ≤ (j:ℝ)⁻¹ := by positivity
  split_ifs <;> linarith [hj.1]

/-- A single diagonal subsequence and a single side work for arbitrarily many kernels. -/
theorem fixed_side {Y : ℕ} (hpnt : PrimeCellInput Y) (hsmooth : FiniteSmoothing Y)
    (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) (q : ℕ → ℕ → Bool) :
    ∃ (σ : ℕ → ℕ) (b : Bool), StrictMono σ ∧
    ∀ H δ η : ℝ, 0 ≤ H → 0 < δ → 0 < η → ∃ D : Finset ℕ,
      KernelFlat D H δ η ∧ ∀ᶠ i in atTop, D ⊆ side Y (X (σ i)) (q (σ i)) b := by
  classical
  obtain ⟨q₀,σ,hσ,hlim⟩ := CompactSpace.tendsto_subseq q
  obtain ⟨b,hdiv⟩ := divergent_color hpnt q₀
  refine ⟨σ,b,hσ,?_⟩
  intro H δ η hH hδ hη
  obtain ⟨c,hc,hbands⟩ := hpnt.2
  obtain ⟨m,hm,hbuild⟩ := hsmooth c H δ η hc hH hδ hη
  let A := bins Y q₀ b
  let ok (j : ℕ) := mass (cell Y j) ≤ 1/2 ∧
    1/(3*(j:ℝ)) ≤ mass (A j) ∧ Bands (A j) j m c
  let g (j : ℕ) := if ok j then mass (A j) else 0
  have hmass (s : Finset ℕ) : 0 ≤ mass s := sum_nonneg fun _ _ => by positivity
  have hg : ¬ Summable g := by
    intro h
    apply hdiv
    apply Summable.of_norm_bounded_eventually_nat (h.mul_left 3)
    filter_upwards [hpnt.1,hbands m] with j hj hb
    have hA : A j ⊆ cell Y j := filter_subset .. 
    by_cases hd : 1/(3*(j:ℝ)) ≤ mass (A j)
    · have hok : ok j := ⟨hj.2,hd,hb (A j) hA hd⟩
      simp only [goodWeight, show bins Y q₀ b j = A j from rfl, if_pos hd, g, if_pos hok,
        Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (j:ℝ)⁻¹ by positivity)]
      have : 3 * (1/(3*(j:ℝ))) = (j:ℝ)⁻¹ := by ring
      linarith
    · have hno : ¬ ok j := fun h => hd h.2.1
      simp only [goodWeight, show bins Y q₀ b j = A j from rfl, if_neg hd,g,if_neg hno,norm_zero,mul_zero,le_refl]
  have hN := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := g) (fun j => by dsimp [g]; split <;> first | exact hmass _ | exact le_rfl)).mp hg
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hN.eventually_ge_atTop (8*(m:ℝ)))
  let J := (range N).filter ok
  have hbudget : 8*(m:ℝ) ≤ ∑ j ∈ J, mass (A j) := by
    simpa [J,sum_filter,g] using hN N le_rfl
  have hA (j : ℕ) : A j ⊆ cell Y j := filter_subset ..
  refine ⟨J.biUnion A,hbuild J A (fun j _ => hA j) (fun j hj => ?_) hbudget,?_⟩
  · obtain ⟨h1,_,h2⟩ := (mem_filter.mp hj).2
    exact ⟨(sum_le_sum_of_subset_of_nonneg (hA j) (fun _ _ _ => by positivity)).trans h1,h2⟩
  · apply (Finset.eventually_all ..).mpr
    intro p hp
    obtain ⟨j,_,hpA⟩ := mem_biUnion.mp hp
    have hpC := mem_filter.mp (hA j hpA)
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hpC.1
    have hc' := (mem_filter.mp hpA).2
    have hq := (tendsto_pi_nhds.mp hlim p).eventually (isOpen_discrete {q₀ p} |>.mem_nhds (Set.mem_singleton _))
    filter_upwards [hq,(hX.comp hσ.tendsto_atTop).eventually_ge_atTop (p:ℝ)] with i hi hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpI).1,Nat.le_floor hx⟩,hpr⟩,
      (show q (σ i) p = q₀ p from hi).trans hc'⟩


end Shift490
end
end

/- Fluctuations -/
section
noncomputable section
namespace Shift490
open Finset MeasureTheory ProbabilityTheory

/-- The second-moment estimate uses only pairwise independence. The variables can be the
success indicators on a product of arbitrary (including countably infinite) cell spaces. -/
theorem few_successes {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h01 : ∀ i ∈ s, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hi : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ)
    {m : ℝ} (hm : 0 < m) (hmean : 4*m ≤ ∑ i ∈ s, ∫ ω, X i ω ∂μ) :
    μ {ω | (∑ i ∈ s, X i ω) < m} ≤ ENNReal.ofReal (1/m) := by
  let T := ∑ i ∈ s, X i
  let M := ∑ i ∈ s, ∫ ω, X i ω ∂μ
  have hM : 4*m ≤ M := hmean
  have hpos : 0 < M := by linarith
  have hT : MemLp T 2 μ := memLp_finsetSum' s hL
  have hE : ∫ ω, T ω ∂μ = M := by
    simp only [T, M, Finset.sum_apply]
    exact integral_finsetSum s fun i hi' => (hL i hi').integrable (by norm_num)
  have hv : variance T μ ≤ M := by
    rw [show T = ∑ i ∈ s, X i from rfl, IndepFun.variance_sum hL hi]
    apply sum_le_sum
    intro i h
    rw [variance_eq_sub (hL i h)]
    have he : X i ^ 2 = X i := by
      funext ω
      rcases h01 i h ω with h' | h' <;> simp [Pi.pow_apply, h']
    rw [he]
    linarith [sq_nonneg (∫ ω, X i ω ∂μ)]
  calc
    _ ≤ μ {ω | M/2 ≤ |T ω - ∫ z, T z ∂μ|} := by
      apply measure_mono
      intro ω h
      change M/2 ≤ |T ω - ∫ z, T z ∂μ|
      have hh : T ω < m := by simpa [T] using h
      rw [hE, abs_of_nonpos (by linarith)]
      linarith
    _ ≤ ENNReal.ofReal (variance T μ / (M/2)^2) :=
      meas_ge_le_variance_div_sq hT (by positivity)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_iff₀ (by positivity) hm).mpr
      nlinarith [mul_le_mul_of_nonneg_right hv hm.le, mul_nonneg hpos.le (sub_nonneg.mpr hM)]

/-- In the product geometric exponent law the all-zero atom has weight ∏(1-q).
Changing a single exponent from zero to one multiplies its weight by q. -/
theorem single_success_weight {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ) :
    (∑ i ∈ s, ∏ j ∈ s, ((1-q j) * q j ^ (if j = i then 1 else 0 : ℕ))) =
      (∏ j ∈ s, (1-q j)) * ∑ i ∈ s, q i := by
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [prod_mul_distrib]
  congr 1
  rw [prod_eq_single_of_mem i hi] <;> simp_all

/-- Lower bound for the probability of success using only reciprocal mass. -/
theorem success_probability_lower {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hsmall : ∑ i ∈ s, q i ≤ 1/2) :
    (∑ i ∈ s, q i)/2 ≤ (∏ i ∈ s, (1-q i)) * ∑ i ∈ s, q i := by
  classical
  have bound (u : Finset ι) (hu : u ⊆ s) :
      1 - ∑ i ∈ u, q i ≤ ∏ i ∈ u, (1-q i) := by
    induction u using Finset.induction with
    | empty => simp
    | insert a u ha ih =>
      have hsub : u ⊆ s := fun i hi => hu (mem_insert_of_mem hi)
      obtain ⟨h0,h1⟩ := hq a (hu (mem_insert_self ..))
      have hs : 0 ≤ ∑ i ∈ u, q i := sum_nonneg fun i hi => (hq i (hsub hi)).1
      rw [sum_insert ha, prod_insert ha]
      exact le_trans (by nlinarith [mul_nonneg h0 hs]) (mul_le_mul_of_nonneg_left
        (ih hsub) (sub_nonneg.mpr h1))
  have hh := bound s (fun _ h => h)
  have hn := sum_nonneg (s := s) fun i hi => (hq i hi).1
  nlinarith [mul_nonneg hn (show 0 ≤ (∏ i ∈ s, (1-q i)) - 1/2 by linarith)]




end Shift490
end
end

/- CellLaw -/
section
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




end Shift490
end
end

/- ProductLaw -/
section
noncomputable section
namespace Shift490
open Finset MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] (A : ι → Finset ℕ)

def join (x : ∀ i, Integers (A i)) : Integers (univ.biUnion A) :=
  ⟨∏ i, (x i).val, by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hdiv
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff ..).mp hdiv
    exact mem_biUnion.mpr ⟨i,mem_univ _,Nat.mem_factoredNumbers'.mp (x i).property p hp hi⟩⟩

theorem join_injective (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Function.Injective (join A) := by
  classical
  intro x y h
  have he : (∏ i, (x i).val) = ∏ i, (y i).val := congrArg Subtype.val h
  have dvd (v z : ∀ i, Integers (A i)) (he : (∏ i, (v i).val) = ∏ i, (z i).val) (i : ι) :
      (v i).val ∣ (z i).val := by
    have hcop : (v i).val.Coprime (∏ k ∈ univ.erase i, (z k).val) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      refine Nat.coprime_of_dvd fun p hp h1 h2 => Finset.disjoint_left.mp (hd (ne_of_mem_erase hk).symm)
        (Nat.mem_factoredNumbers'.mp (v i).property p hp h1)
        (Nat.mem_factoredNumbers'.mp (z k).property p hp h2)
    apply hcop.dvd_of_dvd_mul_right
    rw [mul_prod_erase univ (fun k => (z k).val) (mem_univ i), ← he]
    exact dvd_prod_of_mem _ (mem_univ i)
  exact funext fun i => Subtype.ext (Nat.dvd_antisymm (dvd x y he i) (dvd y x he.symm i))

omit [Fintype ι] in
lemma P_biUnion (s : Finset ι) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    P (s.biUnion A) = ∏ i ∈ s, P (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [P]
  | insert i s hi ih =>
    rw [biUnion_insert,prod_insert hi,P_union _,ih]
    exact disjoint_left.mpr fun p hp hh => by
      obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hh
      exact disjoint_left.mp (hd (by rintro rfl; contradiction)) hp hpk

theorem product_law (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (Measure.pi fun i => law (A i)).map (join A) = law (univ.biUnion A) := by
  classical
  let μ := Measure.pi fun i => law (A i)
  let ν := law (univ.biUnion A)
  have hmeas : Measurable (join A) := measurable_of_countable _
  have : IsProbabilityMeasure (μ.map (join A)) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have atom_eq (x : ∀ i, Integers (A i)) : μ {x} = ν {join A x} := by
    rw [Measure.pi_singleton,law_atom]
    simp only [law_atom]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg (x i))]
    congr 1
    simp [harmonic, join, P_biUnion A _ hd,prod_div_distrib,prod_inv_distrib]
  change μ.map (join A) = ν
  apply Measure.eq_of_le_of_measure_univ_eq _ (by simp [ν])
  apply Measure.le_iff.mpr
  intro s hs
  rw [← Measure.tsum_indicator_apply_singleton (μ.map (join A)) s hs, ← Measure.tsum_indicator_apply_singleton ν s hs]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    by_cases hx : ∃ x, join A x = a
    · obtain ⟨x,rfl⟩ := hx
      have hpre : (join A) ⁻¹' {join A x} = {x} := by
        ext y; exact (join_injective A hd).eq_iff
      rw [hpre]
      exact (atom_eq x).le
    · have hem : (join A) ⁻¹' {a} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hh => hx ⟨x,hh⟩
      simp [hem]
  · simp [ha]


end Shift490
end
end

/- Components -/
section
noncomputable section
namespace Shift490
open Finset MeasureTheory Filter

/-- A finite product is partitioned by choosing m successful coordinates and recording
the values of every other coordinate. The choice is a function only of the success set. -/
def select {ι : Type*} (m : ℕ) (s : Finset ι) : Finset ι :=
  if h : m ≤ s.card then (exists_subset_card_eq h).choose else ∅

lemma select_sub {ι : Type*} (m : ℕ) (s : Finset ι) : select m s ⊆ s := by
  unfold select; split <;> rename_i h
  · exact (exists_subset_card_eq h).choose_spec.1
  · exact empty_subset _

lemma select_size {ι : Type*} {m : ℕ} {s : Finset ι} (h : m ≤ s.card) :
    (select m s).card = m := by simp only [select,dif_pos h]; exact (exists_subset_card_eq h).choose_spec.2

section Rectangles
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, DecidableEq (V i)]
    (G : ∀ i, Finset (V i)) (m : ℕ)

def successes (x : ∀ i, V i) := univ.filter (fun i => x i ∈ G i)
def allowed (x : ∀ i, V i) (i : ι) : Finset (V i) :=
  if i ∈ select m (successes G x) then G i else {x i}
def component (x : ∀ i, V i) := Fintype.piFinset (allowed G m x)

lemma self_mem_component (x : ∀ i, V i) : x ∈ component G m x := by
  apply Fintype.mem_piFinset.mpr
  intro i
  dsimp [allowed]
  split_ifs with h
  · exact (mem_filter.mp (select_sub m _ h)).2
  · simp

lemma component_successes {x y : ∀ i, V i} (h : y ∈ component G m x) :
    successes G y = successes G x := by
  ext i
  have hi := Fintype.mem_piFinset.mp h i
  by_cases hs : i ∈ select m (successes G x)
  · have hg := (mem_filter.mp (select_sub m _ hs)).2
    simp only [allowed,if_pos hs] at hi
    simp [successes,hi,hg]
  · simp only [allowed,if_neg hs,mem_singleton] at hi
    simp [successes,hi]

lemma component_eq {x y : ∀ i, V i} (h : y ∈ component G m x) :
    component G m y = component G m x := by
  have he := component_successes G m h
  apply congrArg Fintype.piFinset
  funext i
  have hi := Fintype.mem_piFinset.mp h i
  dsimp [allowed]
  rw [he]
  split_ifs with hs
  · rfl
  · simp only [allowed,if_neg hs,mem_singleton] at hi
    rw [hi]

end Rectangles

/-- Reassemble conditional bounds over countably many finite rectangles by countable
additivity. The bound can include a separate error on the exceptional rectangles. -/
theorem integrate_components {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) (C : Ω → Finset Ω)
    (self : ∀ x, x ∈ C x) (same : ∀ x y, y ∈ C x → C y = C x)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (localBound : ∀ x, ∑ y ∈ C x, μ.real {y} * f y ≤ ∑ y ∈ C x, μ.real {y} * g y) :
    ∫ y, f y ∂μ ≤ ∫ y, g y ∂μ := by
  classical
  let S (k : Set.range C) : Set Ω := ↑k.val
  have hmeas (k) : MeasurableSet (S k) := (Set.to_countable _).measurableSet
  have disj : Pairwise (Function.onFun Disjoint S) := by
    intro k l h
    apply Set.disjoint_left.mpr
    intro y hk hl
    obtain ⟨x,hx⟩ := k.property
    obtain ⟨z,hz⟩ := l.property
    apply h
    apply Subtype.ext
    exact hx ▸ hz ▸ ((same x y (hx.symm ▸ hk)).symm.trans (same z y (hz.symm ▸ hl)))
  have hu : ⋃ k, S k = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.mpr ⟨⟨C x,⟨x,rfl⟩⟩,self x⟩
  have part {v : Ω → ℝ} (hv : Integrable v μ) :
      HasSum (fun k => ∫ y in S k, v y ∂μ) (∫ y, v y ∂μ) := by
    simpa only [hu,Measure.restrict_univ] using hasSum_integral_iUnion hmeas disj
      (hv.integrableOn (s := ⋃ k, S k))
  apply hasSum_le _ (part hf) (part hg)
  rintro ⟨k,x,rfl⟩
  simpa only [S,setIntegral_finset _ hf.integrableOn,setIntegral_finset _ hg.integrableOn,smul_eq_mul]
    using localBound x


end Shift490
end
end

/- Assembly -/
section
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


end Shift490
end
end

/- Fourier -/
section
noncomputable section
namespace Shift490
open MeasureTheory Real Finset

/-- The finite product can be the characteristic function of any independent selected
cells. Frequencies use exp(i t x), so a Plancherel conversion may carry a constant. -/
theorem spectral_energy {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℂ) (K : ℝ → ℂ)
    {c A : ℝ} (hc : 0 < c) (hm : 0 < s.card) (hk : ∀ t, ‖K t‖ ≤ A)
    (low : ∀ i ∈ s, ∀ t : ℝ, |t| ≤ 1 → ‖φ i t‖ ≤ exp (-c*t^2))
    (mid : ∀ i ∈ s, ∀ t : ℝ, 1 < |t| → |t| ≤ (s.card:ℝ)^2 → ‖φ i t‖ ≤ exp (-c))
    (unit : ∀ i ∈ s, ∀ t, ‖φ i t‖ ≤ 1)
    (hφ : ∀ i ∈ s, Continuous (φ i)) (hK : Continuous K)
    (I₂ : Integrable (fun t : ℝ => t^2 * ‖K t‖^2))
    (I₃ : Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2))) :
    let m : ℝ := s.card
    (∫ t : ℝ, t^2 * ‖K t‖^2 * ‖∏ i ∈ s, φ i t‖^2) ≤
      A^2 / (c*m) * √(π/(c*m)) +
      (c*m)⁻¹^2 * (∫ t : ℝ, t^2 * ‖K t‖^2) +
      (m^2)⁻¹ * (∫ t : ℝ, |t| * (t^2 * ‖K t‖^2)) := by
  let m : ℝ := s.card
  have hm' : 0 < m := by dsimp [m]; exact_mod_cast hm
  let b := c*m
  have hb : 0 < b := mul_pos hc hm'
  let W (t : ℝ) := t^2 * ‖K t‖^2
  let U (t : ℝ) := A^2/b * exp (-b*t^2)
  let V (t : ℝ) := b⁻¹^2 * W t
  let Z (t : ℝ) := (m^2)⁻¹ * (|t| * W t)
  let E (t : ℝ) := W t * ‖∏ i ∈ s, φ i t‖^2
  have major (t : ℝ) : E t ≤ U t + V t + Z t := by
    have hW : 0 ≤ W t := by dsimp [W]; positivity
    have hu : 0 ≤ U t := by dsimp [U]; positivity
    have hv : 0 ≤ V t := by dsimp [V]; positivity
    have hz : 0 ≤ Z t := by dsimp [Z]; positivity
    have prod_bound (r : ℝ) (h : ∀ i ∈ s, ‖φ i t‖ ≤ exp r) :
        ‖∏ i ∈ s, φ i t‖ ≤ exp (m*r) := by
      rw [norm_prod, show exp (m*r) = (exp r)^s.card from Real.exp_nat_mul r s.card]
      simpa using prod_le_prod (fun i _ => norm_nonneg (φ i t)) h
    by_cases h1 : |t| ≤ 1
    · have hh := prod_bound _ (fun i hi => low i hi t h1)
      rw [show m*(-c*t^2) = -(b*t^2) by dsimp [b]; ring, exp_neg] at hh
      have hx : b*t^2 ≤ exp (b*t^2) := (lt_add_one _).le.trans (Real.add_one_le_exp _)
      have hki := pow_le_pow_left₀ (norm_nonneg _) (hk t) 2
      have hE : E t ≤ U t := by
        calc
          E t ≤ t^2 * A^2 * ((exp (b*t^2))⁻¹)^2 := by
            dsimp [E,W]; gcongr
          _ ≤ U t := by
            dsimp [U]
            rw [neg_mul, exp_neg]
            field_simp
            rw [mul_comm b] at hx
            nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg A)]
      linarith
    · by_cases h2 : |t| ≤ m^2
      · have hh := prod_bound _ (fun i hi => mid i hi t (lt_of_not_ge h1) h2)
        rw [show m*(-c) = -b by dsimp [b]; ring, exp_neg] at hh
        have hi := (inv_le_inv₀ (exp_pos b) hb).mpr
          ((lt_add_one b).le.trans (Real.add_one_le_exp b))
        have hE : E t ≤ V t := by
          dsimp [E,V]
          rw [mul_comm (b⁻¹^2)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hh.trans hi) 2) hW
        linarith
      · have hh := prod_bound 0 (by simpa using fun i hi => unit i hi t)
        simp only [mul_zero, exp_zero] at hh
        have hE : E t ≤ W t := by
          simpa [E] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hW
        have hZ : W t ≤ Z t := by
          dsimp [Z]
          rw [← mul_assoc]
          calc
            _ = 1 * W t := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [inv_mul_eq_div]; exact (one_le_div (by positivity)).mpr (le_of_not_ge h2)) hW
        linarith
  have iu : Integrable U := (integrable_exp_neg_mul_sq hb).const_mul _
  have iv : Integrable V := I₂.const_mul _
  have iz : Integrable Z := I₃.const_mul _
  have iM := (iu.add iv).add iz
  have ce : Continuous E := by
    dsimp [E,W]
    fun_prop (disch := assumption)
  have ie : Integrable E := iM.mono' ce.aestronglyMeasurable (ae_of_all _ fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [E,W]; positivity)]
    exact major t)
  change (∫ t, E t) ≤ _
  calc
    _ ≤ ∫ t, (U t + V t + Z t) := integral_mono ie iM major
    _ = _ := by
      have iuv : Integrable (fun t => U t + V t) := iu.add iv
      rw [integral_add iuv iz, integral_add iu iv]
      simp only [U,V,Z,W,integral_const_mul,integral_gaussian,b,m]


end Shift490
end
end

/- Grid -/
section
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



end Shift490
end
end

/- CellSpectrum -/
section
noncomputable section
namespace Shift490
open Finset Real Filter
open scoped BigOperators

abbrev offset (j p : ℕ) : ℝ := log p-j

/-- A rectangular upper discrepancy for the entire prime cell suffices. The data are
uncolored. The mass lower bound is only needed for choosing one of the two sides. -/
def RectanglePNT (Y : ℕ) : Prop :=
  (∀ᶠ j : ℕ in atTop, 2/(3*(j:ℝ)) ≤ mass (cell Y j) ∧ mass (cell Y j) ≤ 1/2) ∧
  ∀ e : ℝ, 0 < e → ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, a ≤ b →
    (j:ℝ) * mass ((cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e

private lemma mono_mass {A B : Finset ℕ} (h : A ⊆ B) : mass A ≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)

private def radius (t : ℝ) := min 1 |t| / 1000
private def residue (x : ℝ) := x - (round (x/(2*π)) : ℝ)*(2*π)

private lemma residue_bound (x : ℝ) : |residue x| ≤ π := by
  have hp := Real.pi_pos
  have hr := mul_le_mul_of_nonneg_right (abs_sub_round (x/(2*π))) (show 0 ≤ 2*π by positivity)
  have ha : |x/(2*π)-(round (x/(2*π)):ℝ)| * (2*π) = |residue x| := by
    calc
      _ = |x/(2*π)-(round (x/(2*π)):ℝ)| * |2*π| := by rw [abs_of_pos (show 0 < 2*π by positivity)]
      _ = _ := by rw [← abs_mul,sub_mul,div_mul_cancel₀ _ (by positivity : 2*π ≠ 0)]; rfl
  rw [ha] at hr
  linarith

private lemma arc_small {Y j : ℕ} {e T : ℝ} (he : 0 < e)
    (heT : e*(2*T+9) ≤ 1/100)
    (hbox : ∀ a b : ℝ, a ≤ b → (j:ℝ)*mass ((cell Y j).filter
      (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e)
    (t α : ℝ) (ht : t ≠ 0) (hf : |t| ≤ T) (ha : |α| ≤ π) :
    (j:ℝ)*mass ((cell Y j).filter (fun p => |residue (t*offset j p-α)| ≤ radius t)) ≤ 1/6 := by
  classical
  let d := radius t / |t|
  have ht' := abs_pos.mpr ht
  have hr : 0 ≤ radius t := by dsimp [radius]; positivity
  have hd : 0 ≤ d := div_nonneg hr ht'.le
  let n : ℤ := ⌈|t|⌉+3
  let ks := Icc (-n) n
  let block (k : ℤ) := (cell Y j).filter (fun p =>
    (α+k*(2*π))/t - d ≤ offset j p ∧ offset j p ≤ (α+k*(2*π))/t + d)
  have sub : ((cell Y j).filter (fun p => |residue (t*offset j p-α)| ≤ radius t)) ⊆ ks.biUnion block := by
    intro p hp
    obtain ⟨hc,hres⟩ := mem_filter.mp hp
    let x := offset j p
    let k := round ((t*x-α)/(2*π))
    have hx : 0 ≤ x ∧ x ≤ 1 := by
      obtain ⟨h1,h2⟩ := (mem_filter.mp hc).2
      dsimp [x,offset]; constructor <;> linarith
    have hR : |t*x-α-k*(2*π)| ≤ π := residue_bound _
    have hdist : |t*x-α| ≤ |t|+π := by
      calc
        _ ≤ |t*x| + |α| := abs_sub _ _
        _ ≤ _ := by rw [abs_mul,abs_of_nonneg hx.1]; nlinarith [mul_nonneg ht'.le (sub_nonneg.mpr hx.2)]
    have hk : |(k:ℝ)| ≤ |t|+2 := by
      have h1 := abs_le.mp hR
      have h2 := abs_le.mp hdist
      have hπ := Real.pi_gt_three
      apply abs_le.mpr
      constructor <;> by_contra! h <;>
        nlinarith [mul_nonneg (show 0 ≤ 2*π-1 by linarith) ht'.le,
          mul_pos (sub_pos.mpr h) (show 0 < 2*π by positivity)]
    have hk' : k ∈ ks := by
      have hceil := Int.le_ceil |t|
      have h₁ : (-n:ℤ) ≤ k := by exact_mod_cast (show ((-n:ℤ):ℝ) ≤ k by dsimp [n]; push_cast; linarith [(abs_le.mp hk).1])
      have h₂ : k ≤ n := by exact_mod_cast (show (k:ℝ) ≤ (n:ℝ) by dsimp [n]; push_cast; linarith [(abs_le.mp hk).2])
      exact mem_Icc.mpr ⟨h₁,h₂⟩
    refine mem_biUnion.mpr ⟨k,hk',mem_filter.mpr ⟨hc,?_⟩⟩
    have hdx : |x-(α+k*(2*π))/t| ≤ d := by
      rw [show x-(α+k*(2*π))/t = (t*x-α-k*(2*π))/t by field_simp; ring,abs_div]
      exact div_le_div_of_nonneg_right hres ht'.le
    exact ⟨by linarith [(abs_le.mp hdx).1],by linarith [(abs_le.mp hdx).2]⟩
  have hcard : (ks.card:ℝ) ≤ 2*|t|+9 := by
    have hn : 0 ≤ n := by dsimp [n]; positivity
    simp only [ks,Int.card_Icc,sub_neg_eq_add]
    rw [show ((n+1+n).toNat:ℝ) = ((n+1+n:ℤ):ℝ) by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ n+1+n by omega)]
    push_cast
    dsimp [n]; push_cast
    linarith [Int.ceil_lt_add_one |t|]
  have hblock (k : ℤ) : (j:ℝ)*mass (block k) ≤ 2*d+e := by
    have hh := hbox ((α+k*(2*π))/t-d) ((α+k*(2*π))/t+d) (by linarith)
    dsimp [block]; linarith
  calc
    _ ≤ (j:ℝ)*mass (ks.biUnion block) := mul_le_mul_of_nonneg_left (mono_mass sub) (by positivity)
    _ ≤ (j:ℝ)*(∑ k ∈ ks, mass (block k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hb (u : Finset ℤ) : mass (u.biUnion block) ≤ ∑ k ∈ u, mass (block k) := by
        induction u using Finset.induction with
        | empty => simp [mass]
        | insert k u hk ih =>
          rw [biUnion_insert,sum_insert hk]
          have hi : mass (block k ∪ u.biUnion block) + mass (block k ∩ u.biUnion block) = mass (block k) + mass (u.biUnion block) := sum_union_inter
          have hn : 0 ≤ mass (block k ∩ u.biUnion block) := sum_nonneg fun _ _ => by positivity
          linarith
      exact hb ks
    _ ≤ ks.card * (2*d+e) := by
      rw [mul_sum]
      simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (s := ks) (fun k _ => hblock k)
    _ ≤ (2*|t|+9)*(2*d+e) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := by
      have hdt : d*|t| = radius t := div_mul_cancel₀ _ ht'.ne'
      have h1 : d ≤ 1/1000 := (div_le_iff₀ ht').mpr (by dsimp [radius]; linarith [min_le_right 1 |t|])
      have h2 : radius t ≤ 1/1000 := by dsimp [radius]; linarith [min_le_left 1 |t|]
      nlinarith [mul_nonneg he.le (sub_nonneg.mpr hf)]

private lemma cos_drop (x : ℝ) : 1 - cos x ≥ (residue x)^2 / 16 := by
  let y := residue x
  have hy : |y| ≤ π := residue_bound _
  have hs := Real.mul_le_sin (x := |y|/2) (by positivity) (by linarith)
  have hs' : |y|/4 ≤ sin (|y|/2) := by
    refine le_trans ?_ hs
    have hπ := Real.pi_lt_four
    field_simp
    nlinarith [mul_nonneg (abs_nonneg y) (show 0 ≤ 4-π by linarith)]
  have hc : cos x = 1 - 2*sin (|y|/2)^2 := by
    rw [← Real.cos_two_mul_eq_one_sub,show 2*(|y|/2)=|y| by ring,Real.cos_abs]
    exact (Real.cos_sub_int_mul_two_pi x _).symm
  rw [hc]
  nlinarith [sq_abs y,pow_le_pow_left₀ (show 0 ≤ |y|/4 by positivity) hs' 2]

private lemma rotate_char (A : Finset ℕ) (j : ℕ) (t : ℝ) (hmass : 0 < mass A) :
    mass A * ‖char A j t‖ = ∑ p ∈ A, (p:ℝ)⁻¹ * cos (t*offset j p - (char A j t).arg) := by
  let z := char A j t
  have harg := Complex.norm_mul_exp_arg_mul_I z
  have he : ((‖z‖ : ℝ):ℂ) = z * Complex.exp (-(z.arg * Complex.I)) := by
    calc
      _ = ((‖z‖:ℝ):ℂ) * (Complex.exp (z.arg * Complex.I) * Complex.exp (-(z.arg * Complex.I))) := by rw [← Complex.exp_add]; simp
      _ = _ := by rw [← mul_assoc,harg]
  have hm : (mass A:ℂ) * z = ∑ p ∈ A, (p:ℂ)⁻¹ * Complex.exp ((t*offset j p : ℝ)*Complex.I) := by
    dsimp only [z,char,offset]
    rw [mul_comm,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hmass.ne')]
  have hrot := congrArg Complex.re (show ((mass A:ℂ) * (‖z‖:ℝ)) =
      ∑ p ∈ A, (p:ℂ)⁻¹ * Complex.exp (((t*offset j p - z.arg:ℝ):ℂ)*Complex.I) by
    rw [he, ← mul_assoc,hm,sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [mul_assoc,← Complex.exp_add,Complex.ofReal_sub,sub_mul,sub_eq_add_neg])
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.re_sum,Complex.exp_ofReal_mul_I_re,← Complex.ofReal_natCast,← Complex.ofReal_inv] at hrot
  exact hrot

theorem prime_cells_of_rectangles {Y : ℕ} (pnt : RectanglePNT Y) : PrimeCellInput Y := by
  refine ⟨pnt.1, (1/32000000:ℝ),by norm_num,?_⟩
  intro m
  let T := max 1 ((m:ℝ)^2)
  let e := (1/100:ℝ)/(2*T+9)
  have hT : 1 ≤ T := le_max_left .. 
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [pnt.2 e he,eventually_gt_atTop 0] with j hbox hj A hA hd
  have hj' : 0 < (j:ℝ) := by exact_mod_cast hj
  have hmass : 0 < mass A := lt_of_lt_of_le (by positivity) hd
  have bd (t : ℝ) (ht : |t| ≤ T) : ‖char A j t‖ ≤ exp (-(radius t)^2/32) := by
    let α := (char A j t).arg
    let B := A.filter (fun p => |residue (t*offset j p-α)| ≤ radius t)
    let C := A \ B
    have hBC : B ⊆ A := filter_subset ..
    have hsplit : mass C + mass B = mass A := sum_sdiff hBC
    have rot := rotate_char A j t hmass
    have loss : mass A * (1-‖char A j t‖) =
        ∑ p ∈ A, (p:ℝ)⁻¹ * (1-cos (t*offset j p-α)) := by
      rw [mul_sub,mul_one,rot]; simp [mul_sub,sum_sub_distrib,mass,α]
    have hn (p : ℕ) : 0 ≤ (p:ℝ)⁻¹*(1-cos (t*offset j p-α)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one _))
    by_cases h0 : t = 0
    · have hh := sum_nonneg (s := A) (fun p _ => hn p)
      rw [← loss] at hh
      subst t
      simpa [radius] using (show ‖char A j 0‖ ≤ 1 by nlinarith)
    have hh := arc_small he (show e*(2*T+9) ≤ 1/100 by dsimp [e]; rw [div_mul_cancel₀ _ (by positivity)])
      hbox t α h0 ht (abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩)
    have hsub := filter_subset_filter (fun p => |residue (t*offset j p-α)| ≤ radius t) hA
    have hmB := mul_le_mul_of_nonneg_left (mono_mass hsub) hj'.le
    have hd' := (div_le_iff₀ (show 0 < 3*(j:ℝ) by positivity)).mp hd
    have hhalf : mass A / 2 ≤ mass C := by
      by_contra! hh'
      nlinarith [mul_pos hj' (show 0 < mass B - mass A/2 by linarith)]
    have hR : 0 ≤ radius t := by dsimp [radius]; positivity
    have hsum : mass C * (radius t^2/16) ≤ mass A * (1-‖char A j t‖) := by
      rw [loss,mass,sum_mul]
      refine le_trans (sum_le_sum ?_) (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ => hn p))
      intro p hp
      obtain ⟨ha,hb⟩ := mem_sdiff.mp hp
      have hlarge : radius t ≤ |residue (t*offset j p-α)| := by
        exact le_of_not_ge (fun hh => hb (mem_filter.mpr ⟨ha,hh⟩))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [cos_drop (t*offset j p-α), sq_abs (residue (t*offset j p-α)),
        pow_le_pow_left₀ hR hlarge 2]
    refine le_trans ?_ (Real.add_one_le_exp _)
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg (radius t)),
      mul_pos hmass (show 0 < ‖char A j t‖ - (-(radius t)^2/32+1) by linarith)]
  constructor
  · intro t ht
    have h := bd t (ht.trans hT)
    convert h using 2
    rw [radius,min_eq_right ht,div_pow,sq_abs]; ring
  · intro t ht hTm
    have h := bd t (hTm.trans (le_max_right ..))
    convert h using 2
    rw [radius,min_eq_left ht.le]; norm_num


end Shift490
end
end

/- PntBridge -/
section
/-
# Prime-cell inputs from the ordinary prime number theorem

The Abel summation lemmas below are from the E490 development's `prime-cells/AbelCells.lean`.
The remaining lemmas obtain the counting limit and the uniform bounded-log-window estimate
from the single hypothesis `θ x / x → 1`.
-/

open Filter Finset Real MeasureTheory Set
open scoped Topology Interval Chebyshev

namespace Erdos490PrimeCells

noncomputable def kernel (x : ℝ) := (x * log x)⁻¹
noncomputable def slope (x : ℝ) := -(log x + 1) / (x ^ 2 * log x ^ 2)

private theorem kernel_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt kernel (slope x) x := by
  have hx' := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')).inv (mul_ne_zero hx0.ne' hx'.ne')
  apply h.congr_deriv
  dsimp [slope]
  field_simp

theorem slope_cont {x : ℝ} (hx : 1 < x) : ContinuousAt slope x := by
  have := (Real.log_pos hx).ne'
  unfold slope
  fun_prop (disch := positivity)

noncomputable def reciprocalInterval (x y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (n : ℝ)⁻¹

theorem abel_reciprocal {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    reciprocalInterval x y =
      kernel y * θ y - kernel x * θ x - ∫ t in x..y, slope t * θ t := by
  let c (n : ℕ) : ℝ := if n.Prime then log n else 0
  have hc (z : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, c n) = θ z := by
    simp [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, c]
  have hk : IntegrableOn (deriv kernel) (Set.Icc x y) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr (f := slope)
    · exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
    · exact fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).deriv
  have ha := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ x) hxy
    (fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).differentiableAt) hk
  simp only [hc, ← intervalIntegral.integral_of_le hxy] at ha
  convert ha using 1
  · unfold reciprocalInterval
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      simp [c,hp,kernel,field]
      exact (div_self (log_pos h).ne').symm
    · simp [c,hp]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    change slope t * θ t = deriv kernel t * θ t
    rw [(kernel_hasDeriv (hx.trans_le ht.1)).deriv]

private theorem primitive_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => (log t)⁻¹ - log (log t)) (slope x * x) x := by
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  have logDer := Real.hasDerivAt_log hx0.ne'
  apply ((logDer.inv hl.ne').sub (logDer.log hl.ne')).congr_deriv
  unfold slope
  field_simp
  ring

theorem abel_main_term {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    kernel y * y - kernel x * x - (∫ t in x..y, slope t * t) =
      log (log y) - log (log x) := by
  have hpt {t : ℝ} (ht : t ∈ Set.uIcc x y) : 1 < t := by
    rw [Set.uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_hasDeriv (hpt ht))
    (ContinuousOn.intervalIntegrable (fun t ht =>
      ((slope_cont (hpt ht)).mul continuousAt_id).continuousWithinAt))]
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  simp [kernel, mul_inv_rev, hx0, hy0]
  ring

/-- The version of the prime number theorem used by the counting and log-window inputs. -/
def ThetaPNT : Prop := Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1)

private theorem theta_error (hθ : ThetaPNT) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, |θ x - x| ≤ δ * x := by
  have h := (tendsto_iff_norm_sub_tendsto_zero.mp hθ).eventually_lt_const hδ
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  change ‖θ x / x - 1‖ < δ at hx
  rw [← div_self hx0.ne', ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hx0] at hx
  exact (div_lt_iff₀ hx0).mp hx |>.le

theorem counting_pnt_of_theta (hθ : ThetaPNT) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x / x) atTop (𝓝 1) := by
  obtain ⟨B, hB, hπ⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.exists_pos
  have herr : Tendsto (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - θ x / log x) *
      (log x / x)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => B / log x) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        (tendsto_const_nhds (x := B) (f := atTop)).mul
          (tendsto_inv_atTop_zero.comp tendsto_log_atTop)
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hπ.bound, eventually_gt_atTop (1 : ℝ)] with x hp hx
    have hx0 : 0 < x := by linarith
    have hl := log_pos hx
    change ‖(Nat.primeCounting ⌊x⌋₊ : ℝ) - θ x / log x‖ ≤ B * ‖x / log x ^ 2‖ at hp
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ x / log x ^ 2)] at hp
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ log x / x)]
    calc
      _ ≤ (B * (x / log x ^ 2)) * (log x / x) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by field_simp
  have h := herr.add hθ
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  field_simp [hx0, (log_pos hx).ne']
  ring

private lemma reciprocal_error_of_theta {x y δ : ℝ} (hx : 1 < x) (hxy : x ≤ y)
    (hθ : ∀ t ∈ Set.Icc x y, |θ t - t| ≤ δ * t) :
    |reciprocalInterval x y - (log (log y) - log (log x))| ≤
      δ * (2 / log x + (log (log y) - log (log x))) := by
  have hpos {t : ℝ} (ht : x ≤ t) : 0 < t := by linarith
  have hlog {t : ℝ} (ht : x ≤ t) : 0 < log t := log_pos (hx.trans_le ht)
  have hs : ContinuousOn slope (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy]
    exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
  have hi : IntervalIntegrable (fun t => slope t * θ t) volume x y :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hs
  have hj : IntervalIntegrable (fun t => slope t * t) volume x y :=
    (hs.mul continuousOn_id).intervalIntegrable
  have herror : IntervalIntegrable (fun t => slope t * (θ t - t)) volume x y := by
    simpa only [mul_sub] using hi.sub hj
  have hkernel {t : ℝ} (ht : t ∈ Set.Icc x y) :
      |kernel t * (θ t - t)| ≤ δ / log t := by
    have ht0 := hpos ht.1
    have hlt := hlog ht.1
    rw [abs_mul, kernel, abs_of_pos (inv_pos.mpr (mul_pos ht0 hlt))]
    calc
      _ ≤ (t * log t)⁻¹ * (δ * t) := by gcongr; exact hθ t ht
      _ = _ := by field_simp
  have hpoint {t : ℝ} (ht : t ∈ Set.Icc x y) :
      |slope t * (θ t - t)| ≤ δ * -(slope t * t) := by
    have ht0 := hpos ht.1
    have hlt := hlog ht.1
    have hst : slope t ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
    rw [abs_mul, abs_of_nonpos hst]
    calc
      _ ≤ (-slope t) * (δ * t) := mul_le_mul_of_nonneg_left (hθ t ht) (neg_nonneg.mpr hst)
      _ = _ := by ring
  have hmain := abel_main_term hx hxy
  have hx0 := hpos le_rfl
  have hy0 := hpos hxy
  have hrep (t : ℝ) (ht : t ≠ 0) : kernel t * t = (log t)⁻¹ := by
    simp [kernel, mul_inv_rev, ht]
  rw [hrep x hx0.ne', hrep y hy0.ne'] at hmain
  have hI : |∫ t in x..y, slope t * (θ t - t)| ≤
      δ * (log (log y) - log (log x) + (log x)⁻¹ - (log y)⁻¹) := by
    apply (intervalIntegral.abs_integral_le_integral_abs hxy).trans
    calc
      _ ≤ ∫ t in x..y, δ * -(slope t * t) :=
        intervalIntegral.integral_mono_on hxy herror.abs (hj.neg.const_mul δ) (fun _ ht => hpoint ht)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg]
        congr 1
        linarith
  rw [abel_reciprocal hx hxy]
  nth_rw 1 [← abel_main_term hx hxy]
  have hrearrange : kernel y * θ y - kernel x * θ x - (∫ t in x..y, slope t * θ t) -
      (kernel y * y - kernel x * x - (∫ t in x..y, slope t * t)) =
      kernel y * (θ y - y) - kernel x * (θ x - x) -
      (∫ t in x..y, slope t * (θ t - t)) := by
    simp only [mul_sub, intervalIntegral.integral_sub hi hj]
    ring
  rw [hrearrange]
  have h1 := abs_sub (kernel y * (θ y - y) - kernel x * (θ x - x))
    (∫ t in x..y, slope t * (θ t - t))
  have h2 := abs_sub (kernel y * (θ y - y)) (kernel x * (θ x - x))
  simp only [div_eq_mul_inv] at hkernel ⊢
  linarith [hkernel ⟨hxy, le_rfl⟩, hkernel ⟨le_rfl, hxy⟩]

private lemma scaled_log_error {s a b : ℝ} (hs : 2 ≤ s) (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    |s * (log (s+b) - log (s+a)) - (b-a)| ≤ 4 / s := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hsa : 0 < s + a := by linarith
  have hsb : 0 < s + b := by linarith
  have hle := log_le_sub_one_of_pos (div_pos hsb hsa)
  have hge := log_le_sub_one_of_pos (div_pos hsa hsb)
  rw [log_div hsb.ne' hsa.ne', ← div_self hsa.ne', ← sub_div] at hle
  rw [log_div hsa.ne' hsb.ne', ← div_self hsb.ne', ← sub_div] at hge
  have happrox (c : ℝ) (hc : |c| ≤ 1) :
      |s * ((b-a) / (s+c)) - (b-a)| ≤ 4 / s := by
    have hsc : 0 < s + c := by linarith [(abs_le.mp hc).1]
    rw [show s * ((b-a) / (s+c)) - (b-a) = -((b-a)*c)/(s+c) by field_simp; ring,
      abs_div, abs_neg, abs_mul, abs_of_nonneg (sub_nonneg.mpr hab), abs_of_pos hsc]
    calc
      _ ≤ 2 / (s+c) := by
        apply div_le_div_of_nonneg_right _ hsc.le
        calc
          _ ≤ (b-a) * 1 := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hab)
          _ ≤ 2 := by linarith
      _ ≤ 4 / s := by
        rw [div_le_div_iff₀ hsc hs0]
        linarith [(abs_le.mp hc).1]
  have h1 := happrox a (abs_le.mpr ⟨ha, hab.trans hb⟩)
  have h2 := happrox b (abs_le.mpr ⟨ha.trans hab, hb⟩)
  rw [show s+b-(s+a) = b-a by ring] at hle
  rw [show s+a-(s+b) = -(b-a) by ring, neg_div] at hge
  exact abs_le.mpr ⟨by linarith [mul_le_mul_of_nonneg_left hge hs0.le, (abs_le.mp h2).1],
    by linarith [mul_le_mul_of_nonneg_left hle hs0.le, (abs_le.mp h1).2]⟩

theorem log_window_uniform_of_theta (hθ : ThetaPNT) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
      |s * reciprocalInterval (exp (s+a)) (exp (s+b)) - (b-a)| ≤ ε := by
  let δ := ε / 16
  have hδ : 0 < δ := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.mp (theta_error hθ hδ)
  have hexp : Tendsto (fun s : ℝ => exp (s - 1)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  filter_upwards [hexp.eventually_ge_atTop X, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (8 / ε)] with s hX' hs hsε a b ha hab hb
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hsa : 0 < s + a := by linarith
  have hsb : 0 < s + b := by linarith
  have hxy : exp (s+a) ≤ exp (s+b) := exp_le_exp.mpr (by linarith)
  have hθ' : ∀ t ∈ Set.Icc (exp (s+a)) (exp (s+b)), |θ t - t| ≤ δ * t :=
    fun t ht => hX t (hX'.trans ((exp_le_exp.mpr (by linarith)).trans ht.1))
  have he := reciprocal_error_of_theta (one_lt_exp_iff.mpr hsa) hxy hθ'
  rw [log_exp, log_exp] at he
  have hL : log (s+b) - log (s+a) ≤ 2 / (s+a) := by
    have h := log_le_sub_one_of_pos (div_pos hsb hsa)
    rw [log_div hsb.ne' hsa.ne', ← div_self hsa.ne', ← sub_div] at h
    apply h.trans
    gcongr
    linarith
  have he' : |reciprocalInterval (exp (s+a)) (exp (s+b)) -
      (log (s+b) - log (s+a))| ≤ δ * (8 / s) := by
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ hδ.le
    calc
      _ ≤ 2 / (s+a) + 2 / (s+a) := add_le_add_right hL _
      _ = 4 / (s+a) := by ring
      _ ≤ 8 / s := by rw [div_le_div_iff₀ hsa hs0]; linarith
  have hsε' : 4 / s ≤ ε / 2 := by
    have hh := (div_le_iff₀ hε).mp hsε
    rw [div_le_iff₀ hs0]
    nlinarith
  rw [show s * reciprocalInterval (exp (s+a)) (exp (s+b)) - (b-a) =
    s * (reciprocalInterval (exp (s+a)) (exp (s+b)) - (log (s+b) - log (s+a))) +
      (s * (log (s+b) - log (s+a)) - (b-a)) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos hs0]
  calc
    _ ≤ s * (δ * (8 / s)) + 4 / s := by gcongr; exact scaled_log_error hs ha hab hb
    _ = 8 * δ + 4 / s := by field_simp
    _ ≤ ε := by dsimp [δ]; linarith

theorem log_window_mass_of_theta (hθ : ThetaPNT) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun s : ℝ => s * reciprocalInterval (exp (s+a)) (exp (s+b)))
      atTop (𝓝 (b-a)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [log_window_uniform_of_theta hθ (half_pos hε)] with s hs
  rw [Real.dist_eq]
  exact (hs a b (by linarith) hab hb).trans_lt (half_lt_self hε)

end Erdos490PrimeCells
end

/- PrimeInput -/
section
/- This adapter reuses `stability-analytic-lean/PrimeInput.lean` with the bounded-log-window
input obtained by Abel summation from the ordinary prime number theorem. -/

noncomputable section
namespace Shift490
open Real Finset Filter Erdos490PrimeCells
open scoped Topology

private lemma interval_upper (hθ : ThetaPNT) {e : ℝ} (he : 0 < e) :
    ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
      (j:ℝ) * reciprocalInterval (exp (j+a)) (exp (j+b)) ≤ b-a+e := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (log_window_uniform_of_theta hθ he)]
    with j hj a b ha hab hb
  have h := (abs_le.mp (hj a b ha hab hb)).2
  linarith

private theorem rect_upper (hθ : ThetaPNT) (Y : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, a ≤ b →
      (j:ℝ)*mass ((cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e := by
  let d := min 1 (e/2)
  have hd : 0 < d := lt_min zero_lt_one (by positivity)
  filter_upwards [interval_upper hθ (e := e/2) (by positivity)] with j h a b hab
  let u := max 0 a
  let v := min 1 b
  let S := (cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)
  have hcoord (p : ℕ) (hp : p ∈ S) : u ≤ offset j p ∧ offset j p ≤ v := by
    obtain ⟨hc,h1,h2⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := (mem_filter.mp hc).2
    exact ⟨max_le (by dsimp [offset]; linarith) h1,le_min (by dsimp [offset]; linarith) h2⟩
  by_cases hne : S.Nonempty
  · obtain ⟨p,hp⟩ := hne
    have huv := (hcoord p hp).1.trans (hcoord p hp).2
    have hv := min_le_left (1:ℝ) b
    have hu := le_max_left (0:ℝ) a
    have hm := h (u-d) v (by linarith [min_le_left (1:ℝ) (e/2)]) (by linarith) hv
    have hsub : S ⊆ (Ioc ⌊exp (j+(u-d))⌋₊ ⌊exp (j+v)⌋₊).filter Nat.Prime := by
      intro k hk
      obtain ⟨hc,_⟩ := mem_filter.mp hk
      have hpr := (mem_filter.mp (mem_filter.mp hc).1).2
      have hk' : 0 < (k:ℝ) := by exact_mod_cast hpr.pos
      have hh := hcoord k hk
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (exp_pos _).le).mpr ?_,Nat.le_floor ?_⟩,hpr⟩
      · apply (Real.lt_log_iff_exp_lt hk').mp
        dsimp [offset] at hh; linarith [hh.1]
      · apply (Real.log_le_iff_le_exp hk').mp
        dsimp [offset] at hh; linarith [hh.2]
    have hle : mass S ≤ reciprocalInterval (exp (j+(u-d))) (exp (j+v)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    change (j:ℝ)*mass S ≤ _
    linarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg j),le_max_right (0:ℝ) a,
      min_le_right (1:ℝ) b,min_le_right (1:ℝ) (e/2)]
  · rw [show (cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b) = ∅ from not_nonempty_iff_eq_empty.mp hne]
    simp [mass]; linarith

theorem rectangle_pnt_of_theta (hθ : ThetaPNT) (Y : ℕ) : RectanglePNT Y := by
  refine ⟨?_,rect_upper hθ Y⟩
  have hlow := (log_window_mass_of_theta hθ (a := 1/10) (b := 9/10) (by norm_num) (by norm_num) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hY := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (Y:ℝ)
  filter_upwards [hlow.eventually (lt_mem_nhds (show (2:ℝ)/3 < 9/10-1/10 by norm_num)),
    rect_upper hθ Y 1 zero_lt_one, hY, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 4]
    with j hlo hup hy hj
  have hj0 : 0 < (j:ℝ) := by linarith
  have hs : (Ioc ⌊exp (j+(1/10:ℝ))⌋₊ ⌊exp (j+(9/10:ℝ))⌋₊).filter Nat.Prime ⊆ cell Y j := by
    intro p hp
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
    have hpp : 0 < (p:ℝ) := by exact_mod_cast hpr.pos
    obtain ⟨hh,hk⟩ := mem_Ioc.mp hpI
    have h1 := (Real.lt_log_iff_exp_lt hpp).mpr (Nat.lt_of_floor_lt hh)
    have h2 := (Real.log_le_iff_le_exp hpp).mpr ((Nat.cast_le.mpr hk).trans (Nat.floor_le (exp_pos _).le))
    have hpy : (Y:ℝ) ≤ p := by
      change (Y:ℝ) ≤ exp j at hy
      exact hy.trans ((exp_le_exp.mpr (by linarith : (j:ℝ) ≤ j+1/10)).trans (Nat.lt_of_floor_lt hh).le)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by exact_mod_cast hpy,
      Nat.le_floor ((Real.log_le_iff_le_exp hpp).mp (by linarith))⟩,hpr⟩,by constructor <;> linarith⟩
  have hh : reciprocalInterval (exp (j+(1/10:ℝ))) (exp (j+(9/10:ℝ))) ≤ mass (cell Y j) :=
    sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  change 2/3 < (j:ℝ)*reciprocalInterval _ _ at hlo
  have hl := mul_le_mul_of_nonneg_left hh hj0.le
  have hu := hup 0 1 (by norm_num)
  rw [filter_eq_self.mpr (fun p hp => by
    obtain ⟨h1,h2⟩ := (mem_filter.mp hp).2
    dsimp [offset]; constructor <;> linarith)] at hu
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · by_contra! h
    nlinarith [mul_pos hj0 (sub_pos.mpr h)]

end Shift490
end
end

/- Bounds -/
section
noncomputable section
namespace Shift490
open Finset Filter

/- The finite Chebyshev argument below is adapted from ../stability-bounded/H3.lean. -/
private noncomputable def smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)

private lemma mem_smooth {n m : ℕ} {P : ℕ → Prop} :
    m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
  classical
  simp [smooth]

private noncomputable def truncatedMass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

private lemma transport {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hm : ∀ a ∈ s, f a ∈ t) (hi : Set.InjOn f s) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  classical
  rw [← sum_image hi]
  apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hm)
  exact fun b _ _ => hg b

private lemma log_sum (n : ℕ) (P : ℕ → Prop) :
    ∑ m ∈ smooth n P, Real.log m ≤
      ((Real.log 4 + 4) * n) * truncatedMass (smooth n P) := by
  classical
  let s := smooth n P
  let U := s.sigma (fun m => m.divisors)
  let V := s.sigma (fun v => Ioc 0 ⌊(n : ℝ) / v⌋₊)
  let f (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.1 / x.2, x.2⟩
  have data {x : Σ _ : ℕ, ℕ} (hx : x ∈ U) :
      x.1 ∈ s ∧ x.2 ∣ x.1 ∧ 0 < x.2 ∧ 0 < x.1 / x.2 := by
    obtain ⟨hm,hd⟩ := mem_sigma.mp hx
    have h0 := Nat.pos_of_mem_divisors hd
    exact ⟨hm, Nat.dvd_of_mem_divisors hd, h0,
      Nat.div_pos (Nat.le_of_dvd (mem_smooth.mp hm).1.1 (Nat.dvd_of_mem_divisors hd)) h0⟩
  have hm : ∀ x ∈ U, f x ∈ V := by
    intro x hx
    obtain ⟨hs,hd,hp,hq⟩ := data hx
    obtain ⟨⟨_,hle⟩,hall⟩ := mem_smooth.mp hs
    refine mem_sigma.mpr ⟨mem_smooth.mpr ⟨⟨hq, (Nat.div_le_self ..).trans hle⟩,
      fun p hpr hdv => hall p hpr (hdv.trans (Nat.div_dvd_of_dvd hd))⟩, ?_⟩
    refine mem_Ioc.mpr ⟨hp, Nat.le_floor ((le_div_iff₀ (by exact_mod_cast hq)).mpr ?_)⟩
    exact_mod_cast (show x.2 * (x.1 / x.2) ≤ n by rwa [Nat.mul_div_cancel' hd])
  have hi : Set.InjOn f U := by
    intro x hx y hy h
    have he := congrArg (fun z : Σ _ : ℕ, ℕ => z.1 * z.2) h
    change x.1 / x.2 * x.2 = y.1 / y.2 * y.2 at he
    rw [Nat.div_mul_cancel (data hx).2.1, Nat.div_mul_cancel (data hy).2.1] at he
    have he' := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
    exact Sigma.ext he (heq_of_eq he')
  calc
    _ = ∑ x ∈ U, ArithmeticFunction.vonMangoldt (f x).2 := by
      simp [U, s, sum_sigma, f, ArithmeticFunction.vonMangoldt_sum]
    _ ≤ ∑ y ∈ V, ArithmeticFunction.vonMangoldt y.2 :=
      transport U V f _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg) hm hi
    _ = ∑ v ∈ s, Chebyshev.psi ((n : ℝ) / v) := by rw [Finset.sum_sigma]; rfl
    _ ≤ ∑ v ∈ s, (Real.log 4 + 4) * ((n : ℝ) / v) :=
      sum_le_sum fun v _ => Chebyshev.psi_le_const_mul_self (by positivity)
    _ = _ := by simp [s, truncatedMass, mul_sum, div_eq_mul_inv, mul_assoc]

theorem F_nonneg (S w) : 0 ≤ F S w := tsum_nonneg atom_nonneg

private theorem countSet_eq (S w) : countSet S w = smooth ⌊Real.exp w⌋₊ (· ∈ S) := by
  classical
  ext n
  simp only [countSet, smooth, mem_filter, mem_range, Nat.lt_succ_iff, mem_Icc]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨⟨Nat.pos_of_ne_zero hn.1,h⟩,Nat.mem_factoredNumbers'.mp hn⟩
  · rintro ⟨⟨_,h⟩,hn⟩
    exact ⟨h,Nat.mem_factoredNumbers'.mpr hn⟩

theorem F_le_one (S w) : F S w ≤ 1 := by
  classical
  rw [F_eq_card,countSet_eq,Real.exp_neg]
  have h := card_le_card (filter_subset (fun m => ∀ p, Nat.Prime p → p ∣ m → p ∈ S)
    (Icc 1 ⌊Real.exp w⌋₊))
  change (smooth ⌊Real.exp w⌋₊ (· ∈ S)).card ≤ _ at h
  simp at h
  rw [inv_mul_eq_div, div_le_one (Real.exp_pos _)]
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.exp_pos w).le)

def K₀ : ℝ := Real.log 4 + 5
lemma K₀_pos : 0 < K₀ := by unfold K₀; positivity

theorem counting_bound (S w) (hw : 0 < w) : F S w ≤ K₀ * P S / w := by
  classical
  let n := ⌊Real.exp w⌋₊
  let t := smooth n (· ∈ S)
  have hm : ∀ k ∈ t, k ∈ Integers S := fun k h => Nat.mem_factoredNumbers'.mpr (mem_smooth.mp h).2
  have hmP : truncatedMass t ≤ P S := by
    let u := t.subtype (· ∈ Integers S)
    have he : ∑ a ∈ u, ((a.val:ℕ):ℝ)⁻¹ = truncatedMass t := by
      exact sum_subtype_of_mem (s := t) (fun n : ℕ => (n:ℝ)⁻¹) hm
    rw [← he, ← (harmonic_sum S).tsum_eq]
    exact (harmonic_sum S).summable.sum_le_tsum u (fun _ _ => by positivity)
  have hnum : (n:ℝ) ≤ Real.exp w := Nat.floor_le (Real.exp_pos _).le
  have hl (k : ℕ) (hk : k ∈ t) : w ≤ Real.log k + Real.exp w * (k:ℝ)⁻¹ := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hm k hk).1
    have := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos w) hk')
    rw [Real.log_div (Real.exp_pos w).ne' hk'.ne', Real.log_exp, div_eq_mul_inv] at this
    linarith
  have hh := sum_le_sum hl
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at hh
  have hlog := log_sum n (· ∈ S)
  have hmass : 0 ≤ truncatedMass t := sum_nonneg fun _ _ => by positivity
  change (∑ k ∈ t, Real.log k) ≤ ((Real.log 4 + 4)*n)*truncatedMass t at hlog
  have hc : (Real.log 4 + 4)*n ≤ (Real.log 4 + 4)*Real.exp w :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  rw [F_eq_card,countSet_eq,Real.exp_neg, inv_mul_eq_div, div_le_div_iff₀ (Real.exp_pos _) hw]
  change t.card * w ≤ _
  calc
    _ ≤ ((Real.log 4 + 4)*Real.exp w)*truncatedMass t + Real.exp w * truncatedMass t := by
      change (t.card : ℝ)*w ≤ (∑ k ∈ t, Real.log k) + Real.exp w * truncatedMass t at hh
      linarith [mul_le_mul_of_nonneg_right hc hmass]
    _ = (K₀ * truncatedMass t) * Real.exp w := by unfold K₀; ring
    _ ≤ _ := by gcongr; exact K₀_pos.le

theorem slow_decrease (S) {w v : ℝ} (h : w ≤ v) : F S w ≤ Real.exp (v-w) * F S v := by
  rw [F_eq_card,F_eq_card,← mul_assoc,← Real.exp_add]
  have hc : countSet S w ⊆ countSet S v := by
    intro n hn
    obtain ⟨h1,h2⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (lt_of_lt_of_le (mem_range.mp h1)
      (Nat.succ_le_succ (Nat.floor_mono (Real.exp_le_exp.mpr h)))),h2⟩
  rw [show v-w + -v = -w by ring]
  gcongr



end Shift490
end
end

/- Transfer -/
section
noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory
open scoped Topology

lemma measurable_F (B : Finset ℕ) : Measurable (F B) := by
  apply Measurable.tsum
  intro a
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

/-- Clip the residual count before testing the smoothed law. Beyond w/2, compensate
using the fixed half moment. The scale of the main error is P(D ∪ B)/w. -/
theorem window_comparison {D B : Finset ℕ} (hd : Disjoint D B) {w H δ η s t : ℝ}
    (hw : 0 < w) (hH : 4*H ≤ w) (hs : |s| ≤ H) (ht : |t| ≤ H)
    (hδ : 0 ≤ δ) (flat : KernelFlat D (H+δ) δ η) :
    F (D ∪ B) (w+s) ≤ F (D ∪ B) (w+t) + P (D ∪ B) / w *
      (4*K₀*((exp δ-1)*2+η) + w * (moment D * exp (-w/4))) := by
  let L := 4*K₀*P B/w
  have hL : 0 < L := div_pos (mul_pos (mul_pos (by norm_num) K₀_pos) (P_pos B)) hw
  let f (x : ℝ) := min 1 (F B (w+x) / L)
  have h01 x : 0 ≤ f x ∧ f x ≤ 1 := ⟨le_min zero_le_one (div_nonneg (F_nonneg ..) hL.le), min_le_left ..⟩
  have hf : Measurable f := measurable_const.min (((measurable_F B).comp
    (measurable_const.add measurable_id)).div_const L)
  have hslow x y (h : x ≤ y) : f x ≤ exp (y-x) * f y := by
    dsimp [f]
    rw [mul_min_of_nonneg _ _ (exp_pos _).le]
    apply le_min
    · simpa using (min_le_left 1 (F B (w+x)/L)).trans (Real.one_le_exp (sub_nonneg.mpr h))
    · have he := slow_decrease B (show w+x ≤ w+y by linarith)
      rw [show w+y-(w+x)=y-x by ring] at he
      exact (min_le_right ..).trans (by rw [← mul_div_assoc]; gcongr)
  have hflat := desmooth flat hf h01 hslow
    (s := s) (t := t) ((abs_add_le ..).trans (by rw [abs_of_nonneg hδ]; linarith))
    (by linarith) hδ
  let R (r v : ℝ) := F B (w+r-v)
  have bound (r v : ℝ) : 0 ≤ R r v ∧ R r v ≤ 1 := ⟨F_nonneg ..,F_le_one ..⟩
  have capped (r v : ℝ) : L*f (r-v) = min L (R r v) := by
    dsimp [f,R]
    rw [mul_min_of_nonneg _ _ hL.le,mul_one,mul_comm L,div_mul_cancel₀ _ hL.ne']
    congr 2; ring
  have scaled (r) : avg D (fun v => min L (R r v)) = L*avg D (fun v => f (r-v)) := by
    rw [← avg_mul]
    exact congrArg _ (funext (fun v => (capped r v).symm))
  have below : L*avg D (fun v => f (t-v)) ≤ avg D (R t) := by
    rw [← scaled]
    exact (avg_summable (D := D) (M := 1) (fun v => ⟨le_min hL.le (bound t v).1,
      (min_le_right ..).trans (bound t v).2⟩)).tsum_le_tsum
      (fun a => mul_le_mul_of_nonneg_left (min_le_right ..) (hnonneg a)) (avg_summable (bound t))
  have point (v : ℝ) : R s v ≤ min L (R s v) + exp (v/2)*exp (-w/4) := by
    by_cases hv : v ≤ w/2
    · have hz : w/4 ≤ w+s-v := by linarith [(abs_le.mp hs).1]
      have hh := counting_bound B (w+s-v) (by linarith)
      have hK := K₀_pos
      have hp := P_pos B
      have hcap : R s v ≤ L := hh.trans (by
        apply (div_le_div_iff₀ (by linarith) hw).mpr
        nlinarith [mul_nonneg (mul_nonneg hK.le hp.le) (show 0 ≤ 4*(w+s-v)-w by linarith)])
      rw [min_eq_right hcap]
      linarith [mul_pos (exp_pos (v/2)) (exp_pos (-w/4))]
    · rw [← exp_add]
      have hh := Real.one_le_exp (show 0 ≤ v/2 + -w/4 by linarith)
      linarith [(bound s v).2, le_min hL.le (bound s v).1]
  have above : avg D (R s) ≤ L*avg D (fun v => f (s-v)) + moment D*exp (-w/4) := by
    rw [← scaled]
    have hcap := avg_summable (D := D) (M := 1) (fun v => ⟨le_min hL.le (bound s v).1,
      (min_le_right ..).trans (bound s v).2⟩)
    apply hasSum_le _ (avg_summable (bound s)).hasSum
      (hcap.hasSum.add ((half_moment D).hasSum.mul_right (exp (-w/4))))
    intro a
    simpa [mul_add,mul_assoc] using mul_le_mul_of_nonneg_left (point (logN a)) (hnonneg a)
  have raw : avg D (R s) ≤ avg D (R t) + L*((exp δ-1)*2+η) + moment D*exp (-w/4) := by
    linarith [mul_le_mul_of_nonneg_left hflat hL.le]
  rw [normalized_convolution hd, normalized_convolution hd, P_union hd]
  change P D * avg D (R s) ≤ P D * avg D (R t) + _
  have htail : 0 ≤ moment D * exp (-w/4) := mul_nonneg
    (tsum_nonneg fun a => mul_nonneg (hnonneg a) (exp_pos _).le) (exp_pos _).le
  have he := mul_le_mul_of_nonneg_left (one_le_P B) htail
  calc
    _ ≤ P D * (avg D (R t) + L*((exp δ-1)*2+η) + P B*(moment D*exp (-w/4))) := by
      apply mul_le_mul_of_nonneg_left _ (P_pos D).le
      linarith
    _ = _ := by dsimp [L]; field_simp; ring


end Shift490
end
end

/- Shift -/
section
noncomputable section
namespace Shift490
open Finset Real Filter
open scoped Topology

/-- Uniform little-o, written with an eventual bound for every point in the window.
The side and subsequence precede both the radius and the error tolerance. -/
def OneColorShift (Y : ℕ) : Prop :=
  ∀ (X : ℕ → ℝ), Tendsto X atTop atTop → ∀ q : ℕ → ℕ → Bool,
    ∃ (σ : ℕ → ℕ) (b : Bool), StrictMono σ ∧
    ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      let C := side Y (X (σ i)) (q (σ i)) b
      let w := log (X (σ i))
      ∀ s : ℝ, |s| ≤ H → |F C (w+s) - F C w| ≤ ε * (P C / w)

theorem one_color_shift {Y : ℕ} (primeCells : PrimeCellInput Y)
    (finiteSmoothing : FiniteSmoothing Y) : OneColorShift Y := by
  intro X hX q
  obtain ⟨σ,b,hσ,hside⟩ := fixed_side primeCells finiteSmoothing X hX q
  refine ⟨σ,b,hσ,?_⟩
  intro H hH ε hε
  let δ := log (1 + ε/(64*K₀))
  let η := ε/(32*K₀)
  have hK := K₀_pos
  have hδ : 0 < δ := Real.log_pos (lt_add_of_pos_right 1 (div_pos hε (by positivity)))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D,hflat,hembed⟩ := hside (H+δ) δ η (by linarith) hδ hη
  let L (i : ℕ) := log (X (σ i))
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp (hX.comp hσ.tendsto_atTop)
  have hquarter : Tendsto (fun i => L i / 4) atTop atTop := hL.atTop_div_const (by norm_num)
  have htail : Tendsto (fun i => L i * (moment D * exp (-L i / 4))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hquarter).const_mul (4*moment D)
    simpa only [mul_zero] using h.congr (fun i => by
      dsimp [Function.comp_def]; rw [pow_one,neg_div]; ring)
  have hbudget : 4*K₀*((exp δ-1)*2+η) = ε/4 := by
    dsimp [δ,η]
    rw [Real.exp_log (by positivity)]
    field_simp
    ring
  filter_upwards [hembed,hL.eventually_gt_atTop (4*H+1),
    htail.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with i hi hlarge hsmall
  let C := side Y (X (σ i)) (q (σ i)) b
  let B := C \ D
  have he : D ∪ B = C := union_sdiff_of_subset hi
  have hd : Disjoint D B := Finset.disjoint_left.mpr (fun _ h₁ h₂ => (mem_sdiff.mp h₂).2 h₁)
  change ∀ s : ℝ, |s| ≤ H → |F C (L i+s) - F C (L i)| ≤ ε * (P C / L i)
  have hpos : 0 < L i := by linarith
  have hE := div_nonneg (P_pos C).le hpos.le
  have compare (s t : ℝ) (hs : |s| ≤ H) (ht : |t| ≤ H) :
      F C (L i+s) ≤ F C (L i+t) + ε*(P C/L i) := by
    have hh := window_comparison hd hpos (by linarith : 4*H ≤ L i) hs ht hδ.le hflat
    rw [he,hbudget] at hh
    have hb : ε/4 + L i * (moment D * exp (-L i/4)) ≤ ε := by
      change L i * (moment D * exp (-L i/4)) < ε/2 at hsmall
      linarith
    linarith [mul_le_mul_of_nonneg_left hb hE]
  intro s hs
  have hz : |(0:ℝ)| ≤ H := by simpa
  have h1 := compare s 0 hs hz
  have h2 := compare 0 s hz hs
  rw [add_zero] at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩



end Shift490
end
end

/- KernelEstimate -/
section
noncomputable section
namespace Shift490
open Finset Real Filter MeasureTheory
open scoped Topology

/- A prime-free, one-dimensional compact-kernel inequality. Frequencies use exp(i*t*x).
Both sides are homogeneous of degree two in the unnormalized finite atom weights. -/
def CompactKernelEstimate : Prop :=
  ∀ δ H : ℝ, 0 < δ → 0 ≤ H → ∃ (κ : Measure ℝ) (K : ℝ → ℂ) (A C : ℝ),
    IsProbabilityMeasure κ ∧ (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧ 0 ≤ C ∧
    Continuous K ∧ (∀ t, ‖K t‖ ≤ A) ∧
    Integrable (fun t : ℝ => t^2 * ‖K t‖^2) ∧
    Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2)) ∧
    ∀ (Ω : Type) (S : Finset Ω) (w v : Ω → ℝ) (a L : ℝ),
      (∀ y ∈ S, 0 ≤ w y ∧ a ≤ v y ∧ v y ≤ a+L) →
      ∀ (f : ℝ → ℝ), Measurable f → (∀ z, 0 ≤ f z ∧ f z ≤ 1) →
      ∀ s r : ℝ, |s| ≤ H → |r| ≤ H →
        (∑ y ∈ S, w y * (testAt κ f s (v y) - testAt κ f r (v y)))^2 ≤
          C * (L+1) * ∫ t : ℝ, t^2 * ‖K t‖^2 * ‖∑ y ∈ S, (w y:ℂ) * phase t (v y)‖^2

private lemma choose_m {c η C A U V : ℝ} (hc : 0 < c) (hη : 0 < η) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ m : ℕ, 0 < m ∧ 1/(m:ℝ) ≤ η/2 ∧
    C*((m:ℝ)+1)*(A^2/(c*m)*√(π/(c*m)) + (c*m)⁻¹^2*U + ((m:ℝ)^2)⁻¹*V) ≤ (η/2)^2 := by
  have hinv : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun m : ℕ => C * (2*A^2/c*√((π/c)*(m:ℝ)⁻¹) +
      (2*U/c^2+2*V)*(m:ℝ)⁻¹)) atTop (𝓝 0) := by
    have hh := ((hinv.const_mul (π/c)).sqrt.const_mul (2*A^2/c)).add (hinv.const_mul (2*U/c^2+2*V))
    simpa using hh.const_mul C
  have hev := hlim.eventually (gt_mem_nhds (show 0 < (η/2)^2 by positivity))
  have hev' := hinv.eventually (gt_mem_nhds (show 0 < η/2 by positivity))
  obtain ⟨m,h1,h2,h3⟩ := (hev.and (hev'.and (eventually_gt_atTop 0))).exists
  refine ⟨m,h3,by simpa only [one_div] using h2.le,?_⟩
  have hm : 1 ≤ (m:ℝ) := by exact_mod_cast h3
  have hn : 0 < (m:ℝ) := by linarith
  calc
    _ ≤ C*(2*m)*(A^2/(c*m)*√(π/(c*m))+(c*m)⁻¹^2*U+((m:ℝ)^2)⁻¹*V) := by gcongr; linarith
    _ = C*(2*A^2/c*√((π/c)*(m:ℝ)⁻¹)+(2*U/c^2+2*V)*(m:ℝ)⁻¹) := by
      rw [show π/(c*m) = (π/c)*(m:ℝ)⁻¹ by ring]
      field_simp; ring
    _ ≤ _ := h1.le

private lemma char_cont (A : Finset ℕ) (j : ℕ) : Continuous (char A j) := by unfold char; fun_prop

private lemma char_le_one (A : Finset ℕ) (j : ℕ) (t : ℝ) : ‖char A j t‖ ≤ 1 := by
  unfold char
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ mass A by apply sum_nonneg; intros; positivity)]
  apply div_le_of_le_mul₀ (by apply sum_nonneg; intros; positivity) zero_le_one
  rw [one_mul]
  refine (norm_sum_le ..).trans ?_
  apply sum_le_sum
  intro p _
  change ‖(p:ℂ)⁻¹ * phase t (log p-j)‖ ≤ _
  rw [norm_mul,norm_phase,mul_one]; simp

theorem successful_of_kernel (kernel : CompactKernelEstimate) (Y : ℕ) : SuccessfulComponents Y := by
  intro c H δ η hc hH hδ hη
  obtain ⟨κ,K,A,C,hκ,hsupp,hC,hK,hA,hI,hJ,hkernel⟩ := kernel δ H hδ hH
  let U := ∫ t : ℝ, t^2*‖K t‖^2
  let V := ∫ t : ℝ, |t| * (t^2*‖K t‖^2)
  obtain ⟨m,hm,hfrac,hbound⟩ := choose_m (A := A) (U := U) (V := V) hc hη hC
    (integral_nonneg (fun _ => by positivity)) (integral_nonneg (fun _ => by positivity))
  refine ⟨m,κ,hm,hfrac,hκ,hsupp,?_⟩
  intro J B hB hband I hcard x f hf h01 s r hs hr
  let R := Fintype.piFinset (rect J B I x)
  let W (y : ∀ j, Integers (B j)) := ∏ j, harmonic (B j) (y j)
  let Z (y : ∀ j, Integers (B j)) := ∑ j, logN (y j)
  let N := ∑ y ∈ R, W y
  have hw (y) : 0 ≤ W y := prod_nonneg (fun i _ => hnonneg (y i))
  have hN : 0 ≤ N := sum_nonneg fun y _ => hw y
  obtain ⟨a,ha⟩ := rect_support J B I hB x
  have he := hkernel _ R W Z a I.card (fun y hy => ⟨hw y,ha y hy⟩) f hf h01 s r hs hr
  have ht := rect_transform J B I (fun i p hp => (mem_filter.mp (mem_filter.mp (hB i hp)).1).2) x
  have hχ (t : ℝ) : ‖∑ y ∈ R, (W y:ℂ)*phase t (Z y)‖ = N*‖∏ i ∈ I, char (B i) i t‖ := ht t
  simp_rw [hχ,mul_pow] at he
  have hfun : (fun t : ℝ => t^2 * ‖K t‖^2 * (N^2 * ‖∏ i ∈ I, char (B i) i t‖^2)) =
      (fun t : ℝ => N^2 * (t^2 * ‖K t‖^2 * ‖∏ i ∈ I, char (B i) i t‖^2)) := by funext t; ring
  rw [hfun,integral_const_mul] at he
  have hE := spectral_energy I (fun i t => char (B i) i t) K hc (hcard ▸ hm) hA
    (fun i _ => (hband i).1) (fun i _ t h1 h2 => (hband i).2 t h1 (hcard ▸ h2))
    (fun i _ t => char_le_one (B i) i t) (fun i _ => char_cont ..) hK hI hJ
  rw [hcard] at hE he
  have hfactor : 0 ≤ C * ((m:ℝ)+1) := by positivity
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hfactor) (sq_nonneg N)
  have hh' := mul_le_mul_of_nonneg_left hbound (sq_nonneg N)
  let d := ∑ y ∈ R, W y * (testAt κ f s (Z y)-testAt κ f r (Z y))
  have dsq : d^2 ≤ (N*(η/2))^2 := by
    dsimp only [U,V] at hh'
    dsimp only [d]; nlinarith only [he,hh,hh']
  have hd : d ≤ N*(η/2) := (abs_le_of_sq_le_sq' dsq (by positivity)).2
  change (∑ y ∈ R, W y * testAt κ f s (Z y)) ≤ ∑ y ∈ R, W y * (testAt κ f r (Z y)+η/2)
  simp only [d,mul_sub,sum_sub_distrib,N] at hd
  simp only [mul_add,sum_add_distrib,← sum_mul]
  linarith

/- The complete stability statement reduced to a pure compact-kernel inequality. -/
end Shift490
end
end

/- BumpKernel -/
section
noncomputable section
namespace Shift490
open Real Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- A smooth, compact probability density and its translated test-integral formula. -/
theorem compact_bump {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Measure ℝ) (g : 𝓢(ℝ,ℂ)), IsProbabilityMeasure κ ∧
      (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧ (∀ u, u ∉ Set.Icc 0 δ → g u = 0) ∧
      ∀ (f : ℝ → ℝ) s z, testAt κ f s z =
        ∫ v : ℝ, f (-v) * (g (v-(z-s))).re := by
  let b : ContDiffBump (δ/2) := ⟨δ/4,δ/2,by positivity,by linarith⟩
  let v := b.normed (volume : Measure ℝ)
  have hn (x) : 0 ≤ v x := b.nonneg_normed _
  have hv : Continuous v := b.continuous_normed
  let ρ (x : ℝ) := ENNReal.ofReal (v x)
  let κ := volume.withDensity ρ
  have hρ : Measurable ρ := hv.measurable.ennreal_ofReal
  have hκ : IsProbabilityMeasure κ := by
    constructor
    change volume.withDensity ρ Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [show (∫⁻ x, ρ x) = ENNReal.ofReal (∫ x, v x) from
      (ofReal_integral_eq_lintegral_ofReal b.integrable_normed (ae_of_all _ hn)).symm,
      b.integral_normed,ENNReal.ofReal_one]
  have supp (x : ℝ) (hx : v x ≠ 0) : x ∈ Set.Icc 0 δ := by
    have hh : x ∈ Function.support v := hx
    rw [show Function.support v = Metric.ball (δ/2) (δ/2) from b.support_normed_eq] at hh
    rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hh
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hsup : HasCompactSupport (fun x => (v x : ℂ)) := HasCompactSupport.comp_left (b.hasCompactSupport_normed (μ := volume)) Complex.ofReal_zero
  let g : 𝓢(ℝ,ℂ) := hsup.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (b.contDiff_normed (μ := volume)))
  refine ⟨κ,g,hκ,(ae_withDensity_iff hρ).mpr (ae_of_all _ fun u hu => supp u (fun hz => hu (by simp [ρ,hz]))),
    fun u hu => ?_,?_⟩
  · change ((v u:ℝ):ℂ) = 0
    exact_mod_cast not_ne_iff.mp (fun h => hu (supp u h))
  · intro f s z
    rw [testAt,integral_withDensity_eq_integral_toReal_smul hρ
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    change (∫ u, (ENNReal.ofReal (v u)).toReal • f (s-z-u)) = _
    simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
    rw [← integral_sub_right_eq_self (fun u => v u * f (s-z-u)) (z-s)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by change v _ * f _ = f _ * v _; rw [mul_comm]; congr 2; ring

/-- Pulling a Schwartz transform back to angular frequency preserves the two required
weighted integrability estimates. -/
theorem angular_weights (g : 𝓢(ℝ,ℂ)) {d : ℝ} (hd : d ≠ 0) :
    let K := fun t : ℝ => g (d*t)
    ∃ A : ℝ, Continuous K ∧ (∀ t, ‖K t‖ ≤ A) ∧
      Integrable (fun t : ℝ => t^2 * ‖K t‖^2) ∧
      Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2)) := by
  let A := SchwartzMap.seminorm ℝ 0 0 g
  have hb (x) : ‖g x‖ ≤ A := g.norm_le_seminorm ℝ _
  have hm (k : ℕ) : Integrable (fun t : ℝ => |t|^k * ‖g (d*t)‖^2) := by
    have h := (integrable_comp_mul_left_iff (fun x : ℝ => ‖x‖^k * ‖g x‖) hd).mpr
      (g.integrable_pow_mul volume k)
    have hdom := h.const_mul (A / |d|^k)
    refine hdom.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_mul,mul_pow]
    have hfac : A / |d|^k * (|d|^k * |t|^k * ‖g (d*t)‖) = |t|^k * (A * ‖g (d*t)‖) := by
      field_simp [abs_ne_zero.mpr hd]
    rw [hfac,pow_two]
    gcongr
    exact hb _
  refine ⟨A,g.continuous.comp (continuous_const.mul continuous_id),fun _ => hb _,?_,?_⟩
  · simpa only [sq_abs] using hm 2
  · exact (hm 3).congr (ae_of_all _ fun t => by dsimp; rw [pow_succ,sq_abs]; ring)

end Shift490
end
end

/- Plancherel -/
section
noncomputable section
namespace Shift490
open Real Filter Finset MeasureTheory
open scoped FourierTransform SchwartzMap Topology

def density {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s : ℝ) : 𝓢(ℝ,ℂ) :=
  ∑ y ∈ S, (w y:ℂ) • g.compSubConstCLM ℂ (z y-s)

lemma density_apply {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s x : ℝ) :
    density g S w z s x = ∑ y ∈ S, (w y:ℂ) * g (x-(z y-s)) := by
  simp [density,SchwartzMap.compSubConstCLM_apply]

private lemma ft_formula (g : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 g ξ = ∫ x, phase (-2*π*ξ) x * g x := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [phase,smul_eq_mul,mul_comm,mul_assoc,mul_left_comm]

private lemma ft_translate (g : 𝓢(ℝ,ℂ)) (a ξ : ℝ) :
    𝓕 (g.compSubConstCLM ℂ a) ξ = phase (-2*π*ξ) a * 𝓕 g ξ := by
  rw [ft_formula,ft_formula,← integral_const_mul]
  let t := -2*π*ξ
  change (∫ x, phase t x * g (x-a)) = ∫ x, phase t a * (phase t x * g x)
  rw [← integral_add_right_eq_self (fun x => phase t x * g (x-a)) a]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by dsimp only; rw [phase_add,add_sub_cancel_right]; ring

private lemma ft_density {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s ξ : ℝ) :
    𝓕 (density g S w z s) ξ =
      (∑ y ∈ S, (w y:ℂ)*phase (-2*π*ξ) (z y)) * 𝓕 g ξ * phase (-2*π*ξ) (-s) := by
  change (SchwartzMap.fourierTransformCLM ℂ (density g S w z s)) ξ = _
  simp only [density,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    SchwartzMap.fourierTransformCLM_apply,ft_translate,smul_eq_mul,sum_mul]
  apply sum_congr rfl
  intro y _
  rw [sub_eq_add_neg,phase_add]; ring

private lemma phase_change (t s r : ℝ) : ‖phase t s-phase t r‖ ≤ 2*|t| * |s-r| := by
  have he : phase t s-phase t r = phase t r * (phase t (s-r)-1) := by
    rw [mul_sub,mul_one,← phase_add,add_sub_cancel]
  rw [he,norm_mul,norm_phase,one_mul]
  by_cases h : |t*(s-r)| ≤ 1
  · have heq : ‖((t*(s-r):ℝ):ℂ)*Complex.I‖ = |t*(s-r)| := by rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hh := Complex.norm_exp_sub_one_le (x := ((t*(s-r):ℝ):ℂ)*Complex.I) (heq ▸ h)
    rw [heq,abs_mul] at hh
    simpa only [phase,mul_assoc] using hh
  · refine (norm_sub_le ..).trans ?_
    rw [norm_one,norm_phase]
    rw [abs_mul] at h
    linarith

lemma schwartz_sq (g : 𝓢(ℝ,ℂ)) : Integrable (fun x => ‖g x‖^2) := by
  apply (g.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 g)).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_right (g.norm_le_seminorm ℝ _) (norm_nonneg _)

theorem density_energy {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s r : ℝ) :
    let k := -2*π
    let E (t : ℝ) := t^2 * ‖𝓕 g (k⁻¹*t)‖^2 * ‖∑ y ∈ S, (w y:ℂ)*phase t (z y)‖^2
    (∫ x : ℝ, ‖(density g S w z s - density g S w z r) x‖^2) ≤
      (2*|s-r|)^2 * |k⁻¹| * ∫ t, E t := by
  intro k E
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let d := density g S w z s - density g S w z r
  have hFT (ξ : ℝ) : 𝓕 d ξ = (∑ y ∈ S, (w y:ℂ)*phase (k*ξ) (z y)) * 𝓕 g ξ *
      (phase (k*ξ) (-s) - phase (k*ξ) (-r)) := by
    change (SchwartzMap.fourierTransformCLM ℂ (density g S w z s - density g S w z r)) ξ = _
    rw [map_sub,_root_.sub_apply,SchwartzMap.fourierTransformCLM_apply,SchwartzMap.fourierTransformCLM_apply,
      ft_density,ft_density,mul_sub]
  have point (ξ : ℝ) : ‖𝓕 d ξ‖^2 ≤ (2*|s-r|)^2 * E (k*ξ) := by
    rw [hFT,norm_mul,norm_mul,mul_pow]
    have hh := phase_change (k*ξ) (-s) (-r)
    rw [show -s- -r = -(s-r) by ring,abs_neg] at hh
    dsimp [E]
    rw [← mul_assoc k⁻¹,inv_mul_cancel₀ hk,one_mul]
    calc
      _ ≤ _ * (2*|k*ξ| * |s-r|)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) (sq_nonneg _)
      _ = _ := by simp only [mul_pow,sq_abs]; ring
  have iE : Integrable E := by
    obtain ⟨_,_,_,hi,_⟩ := angular_weights (𝓕 g) (inv_ne_zero hk)
    let N := ∑ y ∈ S, |w y|
    apply (hi.mul_const (N^2)).mono' (by dsimp [E,phase]; fun_prop)
    apply ae_of_all
    intro t
    dsimp [E]
    rw [abs_of_nonneg (by positivity)]
    gcongr
    refine (norm_sum_le ..).trans (sum_le_sum fun y _ => ?_)
    rw [norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [← SchwartzMap.integral_norm_sq_fourier d]
  have hi := (integrable_comp_mul_left_iff E hk).mpr iE
  calc
    _ ≤ ∫ ξ : ℝ, (2*|s-r|)^2 * E (k*ξ) := integral_mono (schwartz_sq (𝓕 d)) (hi.const_mul _) point
    _ = _ := by rw [integral_const_mul,Measure.integral_comp_mul_left,smul_eq_mul,mul_assoc]


end Shift490
end
end

/- Stability -/
section
noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory
open scoped FourierTransform SchwartzMap Topology ENNReal

private lemma supported_sq (d : 𝓢(ℝ,ℂ)) {a b : ℝ} (hab : a < b)
    (hs : ∀ x, x ∉ Set.Icc a b → d x = 0) :
    (∫ x, ‖d x‖)^2 ≤ (b-a) * ∫ x, ‖d x‖^2 := by
  let U := Set.Icc a b
  let c := (∫ x, ‖d x‖)/(b-a)
  have h1 : ∫ x in U, ‖d x‖ = ∫ x, ‖d x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; rw [hs x hx,norm_zero]
  have h2 : ∫ x in U, ‖d x‖^2 = ∫ x, ‖d x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; rw [hs x hx,norm_zero]; norm_num
  have hvol : volume.real U = b-a := by simp [U,Real.volume_real_Icc_of_le hab.le]
  have hint : IntegrableOn (fun x => ‖d x‖^2) U := (schwartz_sq d).integrableOn
  have hi1 : IntegrableOn (fun x => 2*c*‖d x‖) U := (d.integrable.norm.const_mul _).integrableOn
  have hi0 : IntegrableOn (fun _ : ℝ => c^2) U := by
    exact integrableOn_const measure_Icc_lt_top.ne
  have hnon : 0 ≤ ∫ x in U, (‖d x‖-c)^2 := integral_nonneg fun x => sq_nonneg _
  simp_rw [show ∀ x : ℝ, (‖d x‖-c)^2 = ‖d x‖^2 - 2*c*‖d x‖ + c^2 by intro; ring] at hnon
  have hsub : IntegrableOn (fun x => ‖d x‖^2 - 2*c*‖d x‖) U := hint.sub hi1
  rw [integral_add hsub hi0,integral_sub hint hi1,integral_const_mul,h1,h2,
    setIntegral_const,smul_eq_mul,hvol] at hnon
  have hlen := sub_pos.mpr hab
  have hmean : c*(b-a) = ∫ x, ‖d x‖ := div_mul_cancel₀ _ hlen.ne'
  nlinarith [mul_nonneg hnon hlen.le,congrArg (fun z : ℝ => z^2) hmean,
    congrArg (fun z : ℝ => z*(∫ x, ‖d x‖)) hmean]

private lemma test_integrable (d : 𝓢(ℝ,ℂ)) {f : ℝ → ℝ} (hf : Measurable f)
    (h01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Integrable (fun x => f (-x)*(d x).re) := by
  apply d.integrable.norm.mono' ((hf.comp measurable_neg).mul (Complex.continuous_re.comp d.continuous).measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  change ‖f (-x)*(d x).re‖ ≤ ‖d x‖
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (h01 _).1]
  simpa using mul_le_mul (h01 (-x)).2 (Complex.abs_re_le_norm (d x)) (abs_nonneg _) zero_le_one

private lemma density_test {κ : Measure ℝ} {g : 𝓢(ℝ,ℂ)}
    (h : ∀ (f : ℝ → ℝ) s z, testAt κ f s z = ∫ x : ℝ, f (-x)*(g (x-(z-s))).re)
    {Ω : Type} (S : Finset Ω) (w z : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (s : ℝ) :
    ∑ y ∈ S, w y * testAt κ f s (z y) = ∫ x : ℝ, f (-x)*(density g S w z s x).re := by
  simp_rw [h,← integral_const_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [density_apply,Complex.re_sum,mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact sum_congr rfl (fun _ _ => by ring)
  · intro y _
    exact (test_integrable (g.compSubConstCLM ℂ (z y-s)) hf h01).const_mul _

theorem compact_kernel_estimate : CompactKernelEstimate := by
  intro δ H hδ hH
  obtain ⟨κ,g,hκ,hAE,hsupp,htest⟩ := compact_bump hδ
  let k := -2*π
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let K (t : ℝ) := 𝓕 g (k⁻¹*t)
  obtain ⟨A,hK,hA,hI,hJ⟩ := angular_weights (𝓕 g) (inv_ne_zero hk)
  let C := (1+δ+2*H)*(4*H)^2*|k⁻¹|
  refine ⟨κ,K,A,C,hκ,hAE,by dsimp [C]; positivity,hK,hA,hI,hJ,?_⟩
  intro Ω S w z a L hdata f hf h01 s r hs hr
  by_cases hne : S.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨y,hy⟩ := hne
  have hL : 0 ≤ L := by linarith [(hdata y hy).2.1,(hdata y hy).2.2]
  let d := density g S w z s - density g S w z r
  have support (q : ℝ) (hq : |q| ≤ H) (x : ℝ) (hx : x ∉ Set.Icc (a-H) (a+L+H+δ)) :
      density g S w z q x = 0 := by
    rw [density_apply]
    apply sum_eq_zero
    intro y hy
    rw [hsupp _ (fun hh => hx ⟨by linarith [hh.1,(hdata y hy).2.1,(abs_le.mp hq).2],
      by linarith [hh.2,(hdata y hy).2.2,(abs_le.mp hq).1]⟩),mul_zero]
  have hsup (x : ℝ) (hx : x ∉ Set.Icc (a-H) (a+L+H+δ)) : d x = 0 := by
    change density g S w z s x - density g S w z r x = _
    rw [support s hs x hx,support r hr x hx,sub_zero]
  have hsq := supported_sq d (by linarith : a-H < a+L+H+δ) hsup
  let E := ∫ t : ℝ, t^2*‖K t‖^2*‖∑ y ∈ S, (w y:ℂ)*phase t (z y)‖^2
  have hE : 0 ≤ E := integral_nonneg fun _ => by positivity
  have hd := density_energy g S w z s r
  change (∫ x, ‖d x‖^2) ≤ (2*|s-r|)^2*|k⁻¹| * E at hd
  have hw : a+L+H+δ-(a-H) ≤ (1+δ+2*H)*(L+1) := by
    nlinarith [mul_nonneg hL (show 0 ≤ δ+2*H by linarith)]
  have hsr : 2*|s-r| ≤ 4*H := by linarith [(abs_sub s r).trans (add_le_add hs hr)]
  have hbound : (∫ x, ‖d x‖)^2 ≤ C*(L+1)*E := by
    calc
      _ ≤ _ := hsq
      _ ≤ ((1+δ+2*H)*(L+1))*((4*H)^2*|k⁻¹| * E) := by
        apply mul_le_mul hw (hd.trans ?_) (integral_nonneg fun _ => sq_nonneg _) (by positivity)
        gcongr
      _ = _ := by dsimp [C]; ring
  simp_rw [mul_sub,sum_sub_distrib,density_test htest S w z f hf h01]
  rw [← integral_sub (test_integrable _ hf h01) (test_integrable _ hf h01)]
  apply le_trans _ hbound
  have hnorm : |∫ x : ℝ, (f (-x)*(density g S w z s x).re - f (-x)*(density g S w z r x).re)| ≤
      ∫ x, ‖d x‖ := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono ((test_integrable _ hf h01).sub (test_integrable _ hf h01)).norm d.integrable.norm
    intro x
    change ‖f (-x)*(density g S w z s x).re - f (-x)*(density g S w z r x).re‖ ≤ ‖d x‖
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg (h01 _).1]
    change f (-x) * |(d x).re| ≤ ‖d x‖
    simpa using mul_le_mul (h01 (-x)).2 (Complex.abs_re_le_norm (d x)) (abs_nonneg _) zero_le_one
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hnorm 2

end Shift490
end
end

open Filter Real
open scoped Topology
private theorem ordinary_theta
    (h : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x-x| ≤ K*x/log x^3) :
    Erdos490PrimeCells.ThetaPNT := by
  obtain ⟨K,hK,h⟩ := h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun x : ℝ => K / log x ^ 3) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by decide : 3 ≠ 0)).comp tendsto_log_atTop |>.const_div_atTop _
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with x hx hx0
  have he : Chebyshev.theta x / x - 1 = (Chebyshev.theta x-x)/x := by field_simp
  rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hx0]
  exact (div_le_iff₀ hx0).mpr (hx.trans_eq (by ring))

open Finset
/-- The Euler product on a side needs no extra primality filter. -/
lemma euler_side (Y : ℕ) (x : ℝ) (q : ℕ → Bool) (b : Bool) :
    Shift490.P (Shift490.side Y x q b) = (∏ p ∈ Shift490.side Y x q b, (1-(p:ℝ)⁻¹)⁻¹) := by
  have hp : ∀ p ∈ Shift490.side Y x q b, Nat.Prime p :=
    fun p h => (mem_filter.mp (mem_filter.mp h).1).2
  simp only [Shift490.P, filter_true_of_mem hp]

theorem OMA.solution : OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.H2 := by
  intro prime
  dsimp only
  have h (Y : ℕ) : Shift490.OneColorShift Y :=
    Shift490.one_color_shift
      (Shift490.prime_cells_of_rectangles (Shift490.rectangle_pnt_of_theta (ordinary_theta prime) Y))
      (Shift490.smoothing_of_successful (Shift490.successful_of_kernel Shift490.compact_kernel_estimate Y))
  intro Y X hX q
  obtain ⟨σ,b,hm,hs⟩ := h Y X hX q
  refine ⟨σ,b,hm,?_⟩
  intro H hH η hη
  filter_upwards [hs H hH η hη] with i hi
  simp only [Shift490.F_eq_card, euler_side] at hi
  simp only [Shift490.countSet, Shift490.Integers, Shift490.side,
    Shift490.primesAt] at hi
  convert! hi using 1


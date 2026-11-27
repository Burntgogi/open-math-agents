import H2
import Harmonic

/-! Explicit analytic interface for H2. The harmonic estimates, two-sided error
calculation and extraction from a bad sequence are unconditional. -/
namespace Erdos490Transfer
open Filter Finset
noncomputable section

private lemma density_nonneg (C n u) : 0 ≤ density C n u := by unfold density; positivity

def envelope (K : ℕ) : ℝ := (Real.log 4+5)*(K:ℝ)

lemma density_le_scale {n K u : ℕ} (hn : 0 < Real.log n) (hu : u ≤ K) (C) :
    density C n u ≤ envelope K * Harmonic.scale C n := by
  have hcard : (semigroup C (n/u)).card ≤ (semigroup C n).card :=
    card_le_card fun h hh => mem_semigroup.mpr ⟨(mem_semigroup.mp hh).1,
      (mem_semigroup.mp hh).2.trans (Nat.div_le_self ..)⟩
  calc
    _ = ((semigroup C (n/u)).card : ℝ)/n*u := by unfold density; ring
    _ ≤ ((semigroup C n).card : ℝ)/n * K := by gcongr
    _ ≤ ((Real.log 4+5)*Harmonic.scale C n) * K := by gcongr; exact Harmonic.count_le hn C
    _ = _ := by unfold envelope; ring

/-- Separate one-color estimates on the whole cofactor window, with reciprocal
dilations. For red as the sparse side one can take a multiplier close to
log m/log n, for blue as the sparse side one can take a red multiplier near 1.
The common coloring d and its multipliers may depend on the frozen instance. -/
def OneColorBounds {Y n m} (K : ℕ) (η : ℝ) (c : Colors Y n) (d : Colors Y m) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ Real.log n*a*b = Real.log m ∧
    (∀ i < K, density c.red n (i+1) ≤ a*density d.red m (i+1) + η*Harmonic.scale c.red n) ∧
    (∀ j < K, density c.blue n (j+1) ≤ b*density d.blue m (j+1) + η*Harmonic.scale c.blue n)

/-- Every increasing sequence of old cutoffs with arbitrary partitions has a
frozen instance admitting the per-color lower estimates at every late new
cutoff. Applying this to tails permits arbitrarily late frozen instances. -/
def AnalyticPrimeColorTransfer : Prop :=
  ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
    ∀ c : (k : ℕ) → Colors Y (N k), ∃ k,
      ∀ᶠ m : ℕ in atTop, ∃ d : Colors Y m, OneColorBounds K η (c k) d

/-- Product loss after truncating both proposed lower bounds at zero. -/
lemma product_loss {x y X Y e f : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : x ≤ X+e) (hb : y ≤ Y+f) : x*y ≤ X*Y + e*y + x*f := by
  let a := min x X
  let b := min y Y
  have ha0 : 0 ≤ a := le_min hx hX
  have hb0 : 0 ≤ b := le_min hy hY
  have hxa : x-a ≤ e := sub_le_iff_le_add'.mpr (by dsimp [a]; rw [min_add]; exact le_min (by linarith) (by linarith))
  have hyb : y-b ≤ f := sub_le_iff_le_add'.mpr (by dsimp [b]; rw [min_add]; exact le_min (by linarith) (by linarith))
  have hp : a*b ≤ X*Y := mul_le_mul (min_le_right ..) (min_le_right ..) hb0 hX
  have hf' : a*f ≤ x*f := mul_le_mul_of_nonneg_right (min_le_left ..) hf
  nlinarith only [hp,mul_le_mul_of_nonneg_right hxa hy,mul_le_mul_of_nonneg_left hyb ha0,hf']

theorem entry_loss {Y n m K} {η : ℝ} {c : Colors Y n} {d : Colors Y m}
    (hc : OneColorBounds K η c d) (hη : 0 ≤ η) (hn : 1 ≤ Real.log n)
    {i j : ℕ} (hi : i < K) (hj : j < K) :
    entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + 6*envelope K*η := by
  let L := Real.log (n:ℝ)
  let P := Harmonic.scale c.red n
  let R := Harmonic.scale c.blue n
  let x := density c.red n (i+1)
  let y := density c.blue n (j+1)
  let X := density d.red m (i+1)
  let Z := density d.blue m (j+1)
  obtain ⟨a,b,ha,hb,he,hr,hs⟩ := hc
  have hP : 0 ≤ P := Harmonic.scale_nonneg ..
  have hR : 0 ≤ R := Harmonic.scale_nonneg ..
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hn
  have hE : 0 ≤ envelope K := by unfold envelope; positivity
  have hx : x ≤ envelope K * P := density_le_scale hL hi c.red
  have hy : y ≤ envelope K * R := density_le_scale hL hj c.blue
  have hpr : L*P*R ≤ 3 := Harmonic.scale_product c.separate hn
  have hraw : x*y ≤ (a*X)*(b*Z) + (η*P)*y + x*(η*R) :=
    product_loss (density_nonneg ..) (density_nonneg ..)
      (mul_nonneg ha (density_nonneg ..)) (mul_nonneg hb (density_nonneg ..))
      (mul_nonneg hη hP) (mul_nonneg hη hR) (hr i hi) (hs j hj)
  have heq : L*a*b = Real.log (m:ℝ) := he
  have hmul : L*x*y ≤ Real.log (m:ℝ)*X*Z + 6*envelope K*η := calc
    _ ≤ L*((a*X)*(b*Z) + (η*P)*y + x*(η*R)) := by rw [mul_assoc]; gcongr
    _ ≤ L*((a*X)*(b*Z) + (η*P)*(envelope K*R) + (envelope K*P)*(η*R)) := by gcongr
    _ = (L*a*b)*X*Z + (2*envelope K*η)*(L*P*R) := by ring
    _ ≤ _ := by rw [heq]; nlinarith only [mul_le_mul_of_nonneg_left hpr (show 0 ≤ 2*envelope K*η by positivity)]
  rw [entry_density c (by omega) (by omega),entry_density d (by omega) (by omega)]
  let den : ℝ := ((i+1:ℕ):ℝ)*((j+1:ℕ):ℝ)
  have hden : 1 ≤ den := by dsimp [den]; exact_mod_cast (Nat.mul_pos (Nat.zero_lt_succ i) (Nat.zero_lt_succ j))
  change L*x*y/den ≤ Real.log (m:ℝ)*X*Z/den + _
  have denpos : 0 < den := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_iff₀ denpos,add_mul,div_mul_cancel₀ _ denpos.ne']
  exact hmul.trans (add_le_add_right (le_mul_of_one_le_right (by positivity) hden) _)

theorem matrix_of_analytic (h : AnalyticPrimeColorTransfer) : MatrixTransfer := by
  classical
  intro Y K δ hδ
  let η := δ/(6*envelope K+1)
  have hE : 0 ≤ envelope K := by unfold envelope; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hcost : 6*envelope K*η ≤ δ := by
    have he : η*(6*envelope K+1)=δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  by_contra hbad
  have hfreq := (not_eventually.mp hbad).and_eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  obtain ⟨N,hN,hfail⟩ := extraction_of_frequently_atTop hfreq
  have fail (k : ℕ) := (hfail k).1
  simp only [not_forall] at fail
  choose c hc using fail
  obtain ⟨k,hk⟩ := h Y K η hη N hN c
  apply hc k
  filter_upwards [hk] with m hm
  obtain ⟨d,hd⟩ := hm
  exact ⟨d,fun i hi j hj => (entry_loss hd hη.le (hfail k).2 hi hj).trans (add_le_add_right hcost _)⟩

theorem site_H2 (h : AnalyticPrimeColorTransfer) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 := site_H2_of_matrix (matrix_of_analytic h)

#print axioms site_H2
end
end Erdos490Transfer

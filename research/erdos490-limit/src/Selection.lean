import Law
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Sequences

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

#print axioms fixed_side
end Shift490

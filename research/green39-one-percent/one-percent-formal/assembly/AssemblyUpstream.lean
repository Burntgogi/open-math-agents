import FormalConjectures.GreensOpenProblems.«39»
import SliceConcentration

/-! The rational upstream proportion is exactly the probability on the uniform slice. -/

open Finset Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

theorem upstream_eq_slice (p k c : ℕ) [NeZero p] (hk : k ≤ p) :
    (proportionCoverable p k c : ℝ) = Concentration.sliceProbability
      (univ : Finset (ZMod p)) k (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A+T=univ) := by
  rw [proportionCoverable, dif_neg (NeZero.ne p),if_neg (not_lt_of_ge hk)]
  unfold Concentration.sliceProbability
  push_cast
  congr 2
  apply congrArg Finset.card
  ext A
  simp only [mem_filter]

theorem exact_negation
    (h : Tendsto (fun p : {q : ℕ // q.Prime} =>
      letI : NeZero p.val := ⟨p.property.ne_zero⟩
      let k := p.val.sqrt
      Concentration.sliceProbability (univ : Finset (ZMod p.val)) k
        (fun A => ∃ T : Finset (ZMod p.val), T.card ≤ ⌊1.01*(k:ℝ)⌋₊ ∧ A+T=univ)) atTop (𝓝 0)) :
    ¬ type_of% @Green39.green_39.variant_101 := by
  intro hup
  let : Nonempty {q : ℕ // q.Prime} := ⟨⟨2,Nat.prime_two⟩⟩
  apply zero_ne_one (tendsto_nhds_unique h _)
  convert hup using 1
  funext p
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  exact (upstream_eq_slice _ _ _ (Nat.sqrt_le_self p.val)).symm

end
end Green39.Assembly
#print axioms Green39.Assembly.exact_negation
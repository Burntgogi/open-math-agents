import EquationFour
import AssemblyModel
import SplitLaws

open scoped BigOperators Classical Pointwise
open Finset Filter Real
open Green39.Assembly Green39.Split OnePercent.Fourier

namespace Green39.Smooth
noncomputable section

theorem ordered_eq_split {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℕ)
    (E : Finset α → Finset α → Prop) :
    probability (orderedPairs s a b) (fun q ↦ E q.1 q.2) = splitProb s a b E := by
  rw [probability_eq_mean_first]
  unfold splitProb splitMean
  simp_rw [sm_event]
  rfl

theorem typical_failure_le {p : ℕ} [NeZero p] (hp : 4 ≤ p) (μ : Law p)
    (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1) (hc : ∀ x, μ x ≤ 2/(10^24*(p.sqrt:ℝ))) :
    probability (orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt))
      (fun q ↦ ¬typical μ q) ≤ paperRate 1 p p.sqrt := by
  let k := p.sqrt
  let c := (51:ℝ)/(100*k)
  let E (A B : Points p) := (k:ℝ)/100000000 < l1 μ (rest k) B ∨
    ∃ v, (1:ℝ)/1000 < ∑ z ∈ B, excess μ A c v z
  have h := eqFourFailure_le ({μ} : Finset (Law p)) id hp
    (by simpa using hn) (by simpa using hm) (by simpa using hc)
  have he : probability (orderedPairs (univ:Points p) (half k) (rest k))
      (fun q ↦ E q.1 q.2) ≤ paperRate 1 p k := by
    rw [ordered_eq_split]
    simpa [eqFourFailure,E,k,c,half,rest] using h
  refine (probability_mono ?_).trans he
  intro q hq hbad
  have h2 := (mem_orderedPairs.mp hq).2.2.2.1
  by_contra hnot
  change ¬ (_ ∨ _) at hnot
  push Not at hnot
  apply hbad
  have hconv (u : ZMod p) : convolution (indicator q.2) μ u = conv μ q.2 u :=
    convolution_indicator _ _ _
  have hsm (z : ZMod p) : smoothed q.1 μ z = conv (fun t ↦ μ (-t)) q.1 z := by
    simp only [smoothed_eq_convolution,convolution_indicator,conv]
  constructor
  · rw [show (0.00000001:ℝ)*(p.sqrt:ℝ) = k/100000000 by dsimp [k]; ring]
    simpa only [hconv,h2,l1,ZMod.card] using hnot.1
  · intro v
    simpa only [excess,← hsm,show c = 0.51/(p.sqrt:ℝ) by dsimp [c,k]; ring,
      show (1:ℝ)/1000 = 0.001 by norm_num] using hnot.2 v

private abbrev Primes := {p : ℕ // p.Prime}
local instance (p : Primes) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The expansions of `Assembly.allLaws` and `Assembly.space` avoid importing the
assembly endpoint back into its own input. The conclusion is definitionally its hsmooth. -/
theorem hsmooth_of_rate (C : (p : {n : ℕ // n.Prime}) → Catalog p.val)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p))
    (hr : ∀ᶠ p : ℕ in atTop, paperRate 1 p p.sqrt ≤ exp (-((p.sqrt:ℝ)^(0.48:ℝ)))) :
    ∀ᶠ p in atTop, ∀ μ ∈ (range (C p).stages).biUnion (C p).laws,
      probability (orderedPairs (univ : Points p.val) (half p.val.sqrt) (rest p.val.sqrt))
        (fun q ↦ ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ))) := by
  have hpr : Tendsto (fun p : {n : ℕ // n.Prime} ↦ p.val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨n,hn,hp⟩ := Nat.exists_infinite_primes b
    exact (eventually_ge_atTop (⟨n,hp⟩ : {n : ℕ // n.Prime})).mono fun _ h ↦ hn.trans h
  filter_upwards [hstage, hpr.eventually_ge_atTop 4, hpr.eventually hr] with p hs h4 hrate μ hμ
  obtain ⟨i,hi,hiμ⟩ := mem_biUnion.mp hμ
  obtain ⟨hn,hm,hc⟩ := hs.capped i (mem_range.mp hi) μ hiμ
  exact (typical_failure_le h4 μ hn hm hc).trans hrate

end
end Green39.Smooth

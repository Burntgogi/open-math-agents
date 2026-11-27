import CatalogLaw
import SingletonRate

open Finset Filter Real
open scoped Classical
open Green39.Assembly Green39.Split

namespace Green39.Smooth
noncomputable section

local instance (p : {n : ℕ // n.Prime}) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The hsmooth input of Assembly.tendsto_zero_of_catalog.
Only the deterministic stage specification is required of the catalog. -/
theorem hsmooth (C : (p : {n : ℕ // n.Prime}) → Catalog p.val)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p)) :
    ∀ᶠ p in atTop, ∀ μ ∈ (range (C p).stages).biUnion (C p).laws,
      probability (orderedPairs (univ : Points p.val) (half p.val.sqrt) (rest p.val.sqrt))
        (fun q ↦ ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ))) :=
  hsmooth_of_rate C hstage singleton_paperRate

end
end Green39.Smooth

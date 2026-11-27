import AssemblyEndpoint
import AssemblyUpstream
import CatalogRates
import CatalogEndpoint

/-! The limiting cover probability for the one-percent variant of Green 39. -/

open Filter Topology Finset Real
open scoped Classical

namespace Green39.OnePercentResult
open Green39.Assembly

local instance (p : Prime) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The proportion of uniformly chosen square-root-size sets covered at the
one-percent budget tends to zero along the primes. -/
theorem coverable_tendsto_zero : Tendsto sliceCover atTop (𝓝 0) := by
  let C : (p : Prime) → Catalog p.val := fun p => concreteCatalog p.val
  have hstage : ∀ᶠ p in atTop, StageSpec (C p) :=
    Eventually.of_forall fun p => concreteCatalog_spec p.val
  have h := concreteCatalog_eventual_bounds (fun p : Prime => p.val) prime_cofinal
  exact tendsto_zero_of_catalog C terminalLogConstant_nonneg hstage
    (h.mono fun _ hx => hx.1) (h.mono fun _ hx => hx.2.1)
    (h.mono fun _ hx => hx.2.2) (Green39.Smooth.hsmooth C hstage)

/-- Negation of the exact one-percent variant in the pinned statement. -/
theorem disproof : ¬ (type_of% @Green39.green_39.variant_101) :=
  exact_negation coverable_tendsto_zero

end Green39.OnePercentResult

#print axioms Green39.OnePercentResult.coverable_tendsto_zero
#print axioms Green39.OnePercentResult.disproof

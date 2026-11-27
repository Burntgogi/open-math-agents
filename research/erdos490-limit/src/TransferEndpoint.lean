import Sampling
import Stability

/-! H2 after discharging the prime-cell discrepancy using the strong PNT. -/
namespace Erdos490Transfer

/-- Only the finite successful-component smoothing estimate and the two-color
sampled recovery estimate remain on this route. -/
theorem site_H2_of_components_and_sample
    (smoothing : ∀ Y, Shift490.SuccessfulComponents Y) (recovery : SampledRecovery) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_sampled
    (fun Y => Shift490.prime_cells_of_rectangles (Shift490.rectangle_pnt Y))
    (fun Y => Shift490.smoothing_of_successful (smoothing Y)) recovery

/-- The shift input can be reduced further to a prime-independent Fourier
estimate for compact probability kernels. -/
theorem site_H2_of_kernel_and_sample
    (kernel : Shift490.CompactKernelEstimate) (recovery : SampledRecovery) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_components_and_sample (Shift490.successful_of_kernel kernel) recovery

/-- With the unconditional shift theorem, only the sampled red/blue
realization on stable sequences is required. -/
theorem site_H2_of_sampled_recovery (recovery : SampledRecovery) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_euler
    (euler_of_stable Shift490.one_color_shift_stability (stableRecovery_of_sampled recovery))

#print axioms site_H2_of_sampled_recovery
#print axioms site_H2_of_components_and_sample
#print axioms site_H2_of_kernel_and_sample
end Erdos490Transfer

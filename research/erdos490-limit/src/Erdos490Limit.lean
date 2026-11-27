import H1
import H3
import FinalTransfer
import RedRealization

/-! Local proof assembly for the exact Erdős 490 limit variant. -/

namespace Erdos490Verified

theorem transfer : OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  Erdos490Transfer.site_H2_of_red_good Erdos490Transfer.red_good_realization

theorem limit_exists : type_of% @Erdos490.erdos_490.variants.limit :=
  OMA.R_Erdos490_erdos_490_variants_limit_R1.main Erdos490Trim.H1 transfer Erdos490Bounded.H3

#print axioms transfer
#print axioms limit_exists

end Erdos490Verified

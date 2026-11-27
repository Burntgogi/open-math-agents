import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1_H2_R2

/-! Check the types of the entire OMA pathway against the original Erdős statement. -/
namespace SiteTransferAudit

theorem hierarchy (trim : OMA.R_Erdos490_erdos_490_variants_limit_R1.H1)
    (prime : OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.H1)
    (shift : OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.H2)
    (recovery : OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.H3)
    (bound : OMA.R_Erdos490_erdos_490_variants_limit_R1.H3) :
    type_of% @Erdos490.erdos_490.variants.limit :=
  OMA.R_Erdos490_erdos_490_variants_limit_R1.main trim
    (OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.main prime shift recovery) bound

end SiteTransferAudit

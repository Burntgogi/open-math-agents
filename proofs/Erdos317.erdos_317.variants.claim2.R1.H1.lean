import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

/-! First step by @Burntgogi. Choose the least prime power above n. Each prime
power dividing a denominator below this endpoint is at most n, so that
denominator already divides the LCM through n. -/

open Finset

theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  classical
  intro n hn
  have hex : ∃ u : ℕ, n < u ∧ IsPrimePow u := by
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hnp, hp.isPrimePow⟩
  let u := Nat.find hex
  obtain ⟨hnu, hu⟩ := Nat.find_spec hex
  refine ⟨u, hnu, hu, Nat.dvd_antisymm ?_ ?_⟩
  · exact lcm_mono (Icc_subset_Icc_right (show n ≤ u - 1 by dsimp [u]; omega))
  · apply Finset.lcm_dvd
    intro d hd
    obtain ⟨hdpos, hdle⟩ := mem_Icc.mp hd
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
    intro p k hp hpd
    cases k with
    | zero => simp
    | succ k =>
      have hpow : IsPrimePow (p ^ (k + 1)) := ⟨p, k + 1, hp.prime, by omega, rfl⟩
      have hle : p ^ (k + 1) ≤ d := Nat.le_of_dvd hdpos hpd
      have hsmall : p ^ (k + 1) ≤ n := by
        by_contra! h
        have hmin : u ≤ p ^ (k + 1) := Nat.find_min' hex ⟨h, hpow⟩
        omega
      exact dvd_lcm (f := id) (mem_Icc.mpr ⟨pow_pos hp.pos _, hsmall⟩)

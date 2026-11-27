import OldStableMass

/-! Exponential-weighted old sparse mass inside a bounded strip.
The cutoff y is chosen after its width and accuracy. -/
namespace Erdos490Transfer
open Finset Real Filter Shift490
open scoped Topology
noncomputable section
open Classical

private lemma window_count {C : Finset ℕ} {a z : ℝ} (ha : a ≤ z) :
    (semigroup C ⌊exp z⌋₊).card =
      (semigroup C ⌊exp a⌋₊).card + (oldWindow C a z).card := by
  let A := semigroup C ⌊exp a⌋₊
  let T := semigroup C ⌊exp z⌋₊
  have sub : A ⊆ T := fun m h => mem_semigroup.mpr ⟨(mem_semigroup.mp h).1,
    (mem_semigroup.mp h).2.trans (Nat.floor_mono (exp_le_exp.mpr ha))⟩
  have eq : oldWindow C a z = T \ A := by
    apply Finset.ext
    intro m
    rw [mem_oldWindow,Finset.mem_sdiff]
    simp only [T,A,mem_semigroup]
    constructor
    · rintro ⟨hm,hl,hr⟩
      have hm0 := nat_pos (⟨m,hm⟩ : Integers C)
      refine ⟨⟨hm,Nat.le_floor ((log_le_iff_le_exp hm0).mp hr)⟩,fun h => hl.not_ge ?_⟩
      exact (log_le_iff_le_exp hm0).mpr ((Nat.le_floor_iff (exp_pos _).le).mp h.2)
    · rintro ⟨⟨hm,hr⟩,hn⟩
      have hm0 := nat_pos (⟨m,hm⟩ : Integers C)
      refine ⟨hm,lt_of_not_ge (fun h => hn ⟨hm,Nat.le_floor ((log_le_iff_le_exp hm0).mp h)⟩),
        (log_le_iff_le_exp hm0).mpr ((Nat.le_floor_iff (exp_pos _).le).mp hr)⟩
  rw [eq,card_sdiff_of_subset sub]
  have := card_le_card sub
  change T.card=A.card+(T.card-A.card)
  omega

/-- Equal weight exp(-z) on each good old integer equals its harmonic
weight times exp(log m-z), as used in the sparse sampling integral. -/
theorem sparse_good_finite (C : Finset ℕ) {a z δ : ℝ} (ha : a ≤ z) (e : ℕ → ℝ) :
    F C z ≤ exp (a-z)*F C a + recMass (badWindow C a z δ e)
      + exp (-z)*(goodWindow C a z δ e).card := by
  let B := badWindow C a z δ e
  have sub : B ⊆ oldWindow C a z := filter_subset ..
  have hbad : exp (-z)*B.card ≤ recMass B := by
    rw [mul_comm,← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro m hm
    obtain ⟨hc,_,hr⟩ := mem_oldWindow.mp (sub hm)
    have h := (log_le_iff_le_exp (nat_pos (⟨m,hc⟩ : Integers C))).mp hr
    rw [exp_neg]
    exact inv_anti₀ (nat_pos (⟨m,hc⟩ : Integers C)) h
  have hgood : (oldWindow C a z).card = B.card+(goodWindow C a z δ e).card := by
    rw [goodWindow,card_sdiff_of_subset sub]
    have := card_le_card sub
    change _=B.card+(_-B.card)
    omega
  rw [F_eq_semigroup,F_eq_semigroup,window_count ha,hgood,Nat.cast_add,Nat.cast_add,
    ← mul_assoc,← exp_add,show a-z+ -a = -z by ring]
  change _ ≤ _ + recMass B + _
  linarith only [hbad]

/-- For every ε a *fixed* width B recovers the sparse density from good
old integers up to ε P(C)/z, uniformly in the old prime coloring. -/
theorem sparse_good_window {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y : ℕ in atTop, ∀ᶠ z : ℝ in atTop,
      ∀ N : ℕ, (N:ℝ) ≤ exp (z*2) → ∀ C ⊆ (Ioc y N).filter Nat.Prime,
      F C z - ε*(P C/z) ≤ exp (-z)*(goodWindow C (z-B) z δ (fun p => c/log p^2)).card := by
  have lim := (tendsto_exp_neg_atTop_nhds_zero.const_mul (2*K₀)).eventually
    (gt_mem_nhds (show 2*K₀*0 < ε/2 by linarith))
  obtain ⟨B,hB,hcut⟩ := ((eventually_gt_atTop (0:ℝ)).and lim).exists
  refine ⟨B,hB,?_⟩
  filter_upwards [old_bad_negligible_of_width B hc hδ (show 0 < ε/2 by positivity)] with y hy
  filter_upwards [hy,eventually_gt_atTop (2*B)] with z hz hzB
  intro N hN C hC
  have bad := hz N hN C hC (z-B) le_rfl
  have half : 0 < z-B := by linarith
  have pos : 0 < z := by linarith
  have count : F C (z-B) ≤ 2*(K₀*P C/z) := (counting_bound _ _ half).trans (by
    rw [← mul_div_assoc,div_le_div_iff₀ half pos]
    nlinarith only [mul_le_mul_of_nonneg_left hzB.le (mul_nonneg K₀_pos.le (P_pos C).le)])
  have low := sparse_good_finite C (by linarith : z-B ≤ z) (δ:=δ) (fun p => c/log p^2)
  rw [show z-B-z = -B by ring] at low
  change 2*K₀*exp (-B) < ε/2 at hcut
  have htail : exp (-B)*F C (z-B) ≤ ε/2*(P C/z) := calc
    _ ≤ exp (-B)*(2*(K₀*P C/z)) := mul_le_mul_of_nonneg_left count (exp_pos _).le
    _ = (2*K₀*exp (-B))*(P C/z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcut.le (div_nonneg (P_pos C).le pos.le)
  linarith only [low,bad,htail]

#print axioms sparse_good_window
end
end Erdos490Transfer

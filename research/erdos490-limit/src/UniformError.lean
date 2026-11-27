import SmoothCount

open Real Filter Finset
open scoped Topology
namespace Erdos490Smooth
open Shift490

noncomputable def signedSum (L : Finset ℕ) (z : ℝ) :=
  ∑ U ∈ L.powerset with (∏ p ∈ U,p) ≤ ⌊exp z⌋₊, (-1:ℝ)^U.card / (∏ p ∈ U,p : ℕ)

theorem smooth_sieve_error (k : ℕ) {U z cap : ℝ} (hk : k ≤ ⌊U⌋₊)
    (hz : 0 < z) (hcap : exp z ≤ cap) :
    let L := smoothLabels ⌊U⌋₊ cap
    |F (smoothLabels k U) z - localProduct (Nat.primesLE k) * signedSum L z| ≤
      (2 ^ (Nat.primesLE k).card + 1) * (K₀ * P L / z) := by
  classical
  let S := Nat.primesLE k
  let L := smoothLabels ⌊U⌋₊ cap
  let T := L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp z⌋₊)
  have hs (p : ℕ) (hp : p ∈ S) := (Nat.mem_primesLE.mp hp).2
  have hl (p : ℕ) (hp : p ∈ L) := (Finset.mem_filter.mp hp).2
  have hd : Disjoint S L := Finset.disjoint_left.mpr fun p hp hq =>
    (not_lt_of_ge ((Nat.mem_primesLE.mp hp).1.trans hk)) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  have hlocal : |localProduct S| ≤ 1 := by
    rw [localProduct, Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro p hp
    have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast (hs p hp).one_le
    have hi := inv_le_one_of_one_le₀ hp1
    exact abs_le.mpr ⟨by linarith, by have := inv_nonneg.mpr (by positivity : (0:ℝ) ≤ p); linarith⟩
  have hsum : |signedSum L z| ≤ T.card := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _V ∈ T, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro V hV
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
        have hp : 0 < ∏ p ∈ V,p := Finset.prod_pos fun p h => (hl p (hsub h)).pos
        rw [abs_div, abs_pow, abs_neg,abs_one,one_pow,abs_of_nonneg (by positivity)]
        exact (div_le_one (by exact_mod_cast hp)).mpr (by exact_mod_cast hp)
      _ = _ := by simp
  let M := localProduct S * signedSum L z
  have hm : |M| ≤ T.card := by
    rw [abs_mul]
    exact (mul_le_mul hlocal hsum (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have herr := truncated_error S L hs hl hd ⌊exp z⌋₊
  change |smallCount (S ∪ L) ⌊exp z⌋₊ - ⌊exp z⌋₊ * localProduct S * signedSum L z| ≤
    2^S.card * (T.card:ℝ) at herr
  have hround : |(⌊exp z⌋₊:ℝ) - exp z| ≤ 1 := by
    have h₁ := Nat.floor_le (exp_pos z).le
    have h₂ := Nat.lt_floor_add_one (exp z)
    rw [abs_le]; constructor <;> linarith
  have hex := calc
    |smallCount (S ∪ L) ⌊exp z⌋₊ - exp z * M| =
      |(smallCount (S ∪ L) ⌊exp z⌋₊ - ⌊exp z⌋₊ * localProduct S * signedSum L z) +
        ((⌊exp z⌋₊:ℝ) - exp z) * M| := by dsimp [M]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2^S.card * (T.card:ℝ) + 1 * (T.card:ℝ) := by
      rw [abs_mul]
      exact add_le_add herr (mul_le_mul hround hm (abs_nonneg _) zero_le_one)
  dsimp only
  rw [smooth_count_eq_sieve_with_cap k hcap]
  change |exp (-z) * smallCount (S ∪ L) ⌊exp z⌋₊ - M| ≤ _
  calc
    _ = exp (-z) * |smallCount (S ∪ L) ⌊exp z⌋₊ - exp z * M| := by
      rw [← abs_of_pos (exp_pos (-z)) , ← abs_mul]
      congr 1
      rw [mul_sub,← mul_assoc,←exp_add,neg_add_cancel,exp_zero,one_mul,abs_of_pos (exp_pos _)]
    _ ≤ exp (-z) * (2 ^ S.card * (T.card:ℝ) + 1 * (T.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hex (exp_pos _).le
    _ = (2 ^ S.card + 1) * (exp (-z) * (T.card:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (supported_subsets_bound hl hz) (by positivity)

#print axioms smooth_sieve_error
end Erdos490Smooth


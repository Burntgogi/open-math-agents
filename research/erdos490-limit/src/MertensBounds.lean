import PrimeNumberTheoremAnd.IEANTN.Mertens
import Mathlib

/-! A finite-cutoff consequence of the Mertens error estimate in PNT+. -/
namespace Erdos490Transfer
open Finset Real

lemma mertens_product_lower : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    c / log n ≤ ∏ p ∈ n.primesLE, (1 - 1/(p:ℝ)) := by
  obtain ⟨C,hC⟩ := Mertens.E₃.abs_le
  let A := |C| / log 2
  refine ⟨exp (-eulerMascheroniConstant) * exp (-A),by positivity,?_⟩
  intro n hn
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < log (n:ℝ) := log_pos (by linarith)
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have herr : |Mertens.E₃ (n:ℝ)| ≤ A := (hC n hn').trans (by
    apply (div_le_div_of_nonneg_right (le_abs_self C) hL.le).trans
    exact div_le_div_of_nonneg_left (abs_nonneg _) h2 (log_le_log (by norm_num) hn'))
  have hp := Mertens.prod_one_minus_div_prime_eq (x:=(n:ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hp
  have hset : (Ioc 0 n).filter Nat.Prime = n.primesLE := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩
  rw [hset] at hp
  rw [hp]
  have hlo := (abs_le.mp herr).1
  gcongr

end Erdos490Transfer

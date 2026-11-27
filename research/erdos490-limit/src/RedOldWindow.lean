import OldTransport
import BlueBins
import RedWindow

/-! Recover all old squarefree products at one sparse-color sample point. -/

namespace Erdos490Transfer
open Finset Filter Real MeasureTheory Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

structure RedWord (S : Finset ℕ) where
  head : ℕ
  mem : head ∈ S
  length : ℕ
  tail : Fin length ≃ ↥(S.erase head)

def wordOfNonempty {S : Finset ℕ} (h : S.Nonempty) : RedWord S where
  head := h.choose
  mem := h.choose_spec
  length := Fintype.card ↥(S.erase h.choose)
  tail := (Fintype.equivFin _).symm

namespace RedWord
variable {S : Finset ℕ} (r : RedWord S)

def digits : List ℕ := r.head :: List.ofFn fun j => (r.tail j).val

lemma sum_digits (f : ℕ → ℝ) :
    (r.digits.map f).sum = ∑ p ∈ S,f p := by
  calc
    _ = f r.head + ∑ j : Fin r.length, f (r.tail j).val := by simp [digits,List.map_ofFn,Function.comp_def,Fin.sum_ofFn]
    _ = f r.head + ∑ j : ↥(S.erase r.head), f j.val := by rw [r.tail.sum_comp (fun j => f j.val)]
    _ = _ := by rw [← Finset.add_sum_erase S f r.mem]; congr 1; simpa only [Finset.attach_eq_univ] using Finset.sum_attach (S.erase r.head) f

lemma prod_digits (f : ℕ → ℝ) :
    f r.head * (∏ j : Fin r.length,f (r.tail j).val) = ∏ p ∈ S,f p := by
  rw [r.tail.prod_comp (fun j => f j.val), ← Finset.mul_prod_erase S f r.mem]
  congr 1
  simpa only [Finset.attach_eq_univ] using Finset.prod_attach (S.erase r.head) f

lemma all_mem {p : ℕ} (h : p ∈ r.digits) : p ∈ S := by
  rcases List.mem_cons.mp h with h|h
  · simpa only [h] using r.mem
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp h
    exact hj ▸ Finset.mem_of_mem_erase (r.tail j).property

def headLabel (b : ℝ) := oldLabel b r.head
def tailLabel (b : ℝ) (j : Fin r.length) := oldLabel b (r.tail j).val

lemma as_law (b : ℝ) : labelSum limitFactor (r.headLabel b :: List.ofFn (r.tailLabel b)) =
    law b r.digits := by simp only [law,digits,List.map_cons,List.map_ofFn]; rfl

lemma support {b δ : ℝ} (e : ℕ → ℝ)
    (hp : ∀ p ∈ S, p.Prime)
    (he : ∀ p ∈ S, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (hδ : ∑ p ∈ S,e p ≤ δ) :
    ∀ᵐ v ∂(labelSum limitFactor (r.headLabel b :: List.ofFn (r.tailLabel b)) : Measure ℝ),
    v ∈ Set.Icc (log ((∏ p ∈ S,p : ℕ):ℝ)-δ) (log ((∏ p ∈ S,p : ℕ):ℝ)+δ) := by
  rw [r.as_law]
  have h := law_displacement b r.digits e (fun p h => by
    have hm := r.all_mem h
    simpa only [oldLabel,dif_pos (hp p hm)] using he p hm)
  rw [Nat.cast_prod,log_prod (fun p hm => by exact_mod_cast (hp p hm).ne_zero)]
  filter_upwards [h] with v hv
  rw [r.sum_digits,r.sum_digits] at hv
  exact ⟨by linarith [(abs_le.mp (hv.trans hδ)).1],by linarith [(abs_le.mp (hv.trans hδ)).2]⟩

lemma harmonic (b : ℝ) (hp : ∀ p ∈ S,p.Prime) :
    harmonicSize (r.headLabel b) * (∏ j,harmonicSize (r.tailLabel b j)) =
      ((∏ p ∈ S,p:ℕ):ℝ)⁻¹ := by
  change harmonicSize (oldLabel b r.head) * (∏ j,harmonicSize (oldLabel b (r.tail j).val)) = _
  rw [r.prod_digits (fun p => harmonicSize (oldLabel b p)),Nat.cast_prod,← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p h
  change log ((oldLabel b p).hi/(oldLabel b p).lo) = _
  simpa only [oldLabel,dif_pos (hp p h),cellLabel] using cell_log_mass b p (hp p h)

end RedWord
/-- For all good old integers simultaneously, select a single log point before choosing
the cofactor offset or the new dilation. Each surviving old integer has exactly the
same weighted contribution exp(-z). -/
theorem red_old_words (G : Finset ℕ) (hne : G.Nonempty)
    (word : (m : G) → RedWord m.val.primeFactors) {b z B δ : ℝ}
    (hB : 0 < B) (hδ : 0 ≤ δ) (e : ℕ → ℝ)
    (hprod : ∀ m : G, (∏ p ∈ m.val.primeFactors,p) = m.val)
    (he : ∀ m : G, ∀ p ∈ m.val.primeFactors, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (herr : ∀ m : G, ∑ p ∈ m.val.primeFactors,e p ≤ δ)
    (hm : ∀ m : G, log (m.val:ℝ) ∈ Set.Icc (z-B) z)
    {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Set.Icc (z-B-δ) (z+δ), x ∉ E ∧ ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      exp (-2*δ)*(exp (-z)*G.card)-ε ≤ t*exp (-(t*x-c))*
        ∑ m : G, finalCount ((word m).headLabel b) ((word m).tailLabel b) t x c := by
  classical
  let y (m : G) := log (m.val:ℝ)
  have hp (m : G) : ∀ p ∈ m.val.primeFactors, p.Prime := fun _ h => Nat.prime_of_mem_primeFactors h
  have hs (m : G) := (word m).support e (hp m) (he m) (herr m)
  have hi : Nonempty ↥G := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have ht := red_window_recovery (Finset.univ : Finset ↥G) Finset.univ_nonempty y
    (fun m => (word m).headLabel b) (fun m => (word m).length) (fun m => (word m).tailLabel b) hB hδ
    (fun m _ => hm m) (fun m _ => by simpa only [hprod m,y] using hs m) hE
  have hterm (m : G) :
      (harmonicSize ((word m).headLabel b) * ∏ j, harmonicSize ((word m).tailLabel b j)) *
        exp (y m-z) = exp (-z) := by
    have hm0 : 0 < m.val := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp (word m).mem).2.2
    rw [(word m).harmonic b (hp m),hprod m,sub_eq_add_neg,exp_add]
    dsimp [y]
    rw [exp_log (by exact_mod_cast hm0),inv_mul_cancel_left₀ (by exact_mod_cast hm0.ne')]
  simpa only [hterm,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
    mul_comm (G.card:ℝ) (exp (-z))] using ht

#print axioms red_old_words


end
end Erdos490Transfer

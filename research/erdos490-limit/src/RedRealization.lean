import RedOldWindow
import RedProducts
import RedScale
import RedGood

/-! The red-color realization on the exact old sparse window, with all new
words counted as distinct integers in the assigned prime semigroup. -/
namespace Erdos490Transfer
open Filter Finset Real Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

private theorem word_finalCount {S : Finset ℕ} (word : RedWord S) (hp : ∀ p ∈ S,p.Prime)
    {b t : ℝ} (ht : 0 < t) (x c : ℝ) :
    finalCount (word.headLabel b) (word.tailLabel b) t x c =
      (((newProducts b t S).filter (· ≤ ⌊exp (t*x-c)⌋₊)).card:ℝ) := by
  have a : word.headLabel b = cellLabel b word.head (hp _ word.mem) := by
    simp only [RedWord.headLabel,oldLabel,dif_pos (hp _ word.mem),cellLabel]
  have g : word.tailLabel b = (fun j => cellLabel b (word.tail j).val
      (hp _ (mem_of_mem_erase (word.tail j).property))) := by
    funext j
    simp only [RedWord.tailLabel,oldLabel,dif_pos (hp _ (mem_of_mem_erase (word.tail j).property)),cellLabel]
  rw [a,g]
  exact finalCount_eq_newProducts_card ht hp word.mem word.tail x c

theorem red_good_realization : RedGoodRealization := by
  intro C hp c hc z B δ hB hδ hpos
  let e (p : ℕ) := c/log p^2
  let G := goodWindow C (z-B) z δ e
  dsimp only
  intro nonempty
  change G.Nonempty at nonempty
  have prop (m : G) := good_properties hp m.property
  have hprod (m : G) : (∏ p ∈ m.val.primeFactors,p) = m.val := (prop m).2.1
  have has (m : G) : m.val.primeFactors.Nonempty := by
    by_contra! hh
    have h1 : m.val = 1 := by simpa only [hh,prod_empty] using (hprod m).symm
    have hl := (prop m).2.2.2.1
    rw [h1,Nat.cast_one,log_one] at hl
    linarith
  let word (m : G) := wordOfNonempty (has m)
  have he (m : G) := fun p (h : p ∈ m.val.primeFactors) v (h' : v ∈ Set.Ioc (boundary Mertens.M p)
    (boundary Mertens.M (p+1))) => hc p ((prop m).1 h) v ⟨h'.1.le,h'.2⟩
  obtain ⟨x,hx,_,hr⟩ := red_old_words G nonempty word hB hδ.le e hprod he
    (fun m => (prop m).2.2.1) (fun m => ⟨(prop m).2.2.2.1.le,(prop m).2.2.2.2⟩) Set.finite_empty
  refine ⟨x,hx,?_⟩
  let mass (t c' : ℝ) := ∑ m : G,finalCount ((word m).headLabel Mertens.M) ((word m).tailLabel Mertens.M) t x c'
  have count {t : ℝ} (ht : 0 < t) (c' : ℝ) : mass t c' ≤
      ((semigroup (bands Mertens.M t C) ⌊exp (t*x-c')⌋₊).card:ℝ) := by
    let cap := ⌊exp (t*x-c')⌋₊
    let f (S : Finset ℕ) := ((newProducts Mertens.M t S).filter (· ≤ cap)).card
    have inj : Set.InjOn Nat.primeFactors G := by
      intro m hm n hn heq
      simpa only [hprod ⟨m,hm⟩,hprod ⟨n,hn⟩] using congrArg (fun S : Finset ℕ => ∏ p ∈ S,p) heq
    have bound := sum_newProducts_card_le_semigroup_card (b:=Mertens.M) ht C (G.image Nat.primeFactors)
      (fun _ h => by obtain ⟨m,hm,rfl⟩ := mem_image.mp h; exact (prop ⟨m,hm⟩).1) cap
    rw [sum_image inj] at bound
    calc
      mass t c' = ∑ m : G,(f m.val.primeFactors:ℝ) := sum_congr rfl (fun m _ =>
        word_finalCount (word m) (fun _ h => Nat.prime_of_mem_primeFactors h) ht x c')
      _ = ↑(∑ m ∈ G,f m.primeFactors) := by
        rw [Nat.cast_sum,← Finset.sum_attach G (fun m => (f m.primeFactors:ℝ)),Finset.attach_eq_univ]
      _ ≤ _ := by exact_mod_cast bound
  have h := red_at_prescribed (show 0 < x from hpos.trans_le hx.1) mass count hr
  simpa only [mul_assoc] using h

#print axioms red_good_realization
end
end Erdos490Transfer

import RedArithmetic

open Real Filter Finset MeasureTheory
open scoped Topology
namespace Erdos490PrimeCells

abbrev PrimeChoices {n : ℕ} (t : ℝ) (L : Fin n → Label) :=
  (j : Fin n) → primeBand t (L j).lo (L j).hi

def choiceProduct {n : ℕ} {t : ℝ} {L : Fin n → Label} (f : PrimeChoices t L) : ℕ :=
  ∏ j, (f j : ℕ)

noncomputable def countedWords {n : ℕ} (i : Label) (L : Fin n → Label) (t : ℝ) (cap : ℕ) :=
  (Finset.univ : Finset (PrimeChoices t L)).sigma (fun f =>
    (primeBand t i.lo i.hi).filter (fun q => choiceProduct f * q ≤ cap))

private theorem lastCell_eq (t z : ℝ) (i : Label) {D : ℕ} (hD : 0 < D) :
    (Finset.Ioc ⌊exp (t*i.lo)⌋₊ ⌊min (exp (t*i.hi)) (exp (z-log (D:ℝ)))⌋₊).filter Nat.Prime =
    (primeBand t i.lo i.hi).filter (fun q => D*q ≤ ⌊exp z⌋₊) := by
  ext q
  simp only [primeBand,Finset.mem_filter,Finset.mem_Ioc,Nat.floor_mono.map_min,le_min_iff]
  have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
  have hcut : q ≤ ⌊exp (z-log (D:ℝ))⌋₊ ↔ D*q ≤ ⌊exp z⌋₊ := by
    rw [Nat.le_floor_iff (exp_pos _).le, Nat.le_floor_iff (exp_pos _).le,exp_sub,exp_log hD',
      le_div_iff₀ hD',Nat.cast_mul,mul_comm (q:ℝ)]
  tauto

theorem finalCount_eq_card {n : ℕ} (i : Label) (L : Fin n → Label) (t x c : ℝ) :
    finalCount i L t x c = (countedWords i L t ⌊exp (t*x-c)⌋₊).card := by
  unfold finalCount countedWords
  rw [Finset.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro f _
  have h0 : 0 < choiceProduct f := Finset.prod_pos fun j _ => (Finset.mem_filter.mp (f j).property).2.pos
  exact congrArg (fun V : Finset ℕ => (V.card:ℝ)) (lastCell_eq t (t*x-c) i h0)

theorem countedWords_lower {n : ℕ} (i : Label) (L : Fin n → Label) (x c : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop,
      (∏ j, log ((L j).hi/(L j).lo)) * labelDensity i (List.ofFn L) x - ε ≤
        t*exp (-(t*x-c))*(countedWords i L t ⌊exp (t*x-c)⌋₊).card := by
  simpa only [finalCount_eq_card] using final_count_lower i L x c hε

#print axioms countedWords_lower
end Erdos490PrimeCells

import CellLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
namespace Shift490
open Finset MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] (A : ι → Finset ℕ)

def join (x : ∀ i, Integers (A i)) : Integers (univ.biUnion A) :=
  ⟨∏ i, (x i).val, by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hdiv
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff ..).mp hdiv
    exact mem_biUnion.mpr ⟨i,mem_univ _,Nat.mem_factoredNumbers'.mp (x i).property p hp hi⟩⟩

theorem join_injective (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Function.Injective (join A) := by
  classical
  intro x y h
  have he : (∏ i, (x i).val) = ∏ i, (y i).val := congrArg Subtype.val h
  have dvd (v z : ∀ i, Integers (A i)) (he : (∏ i, (v i).val) = ∏ i, (z i).val) (i : ι) :
      (v i).val ∣ (z i).val := by
    have hcop : (v i).val.Coprime (∏ k ∈ univ.erase i, (z k).val) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      refine Nat.coprime_of_dvd fun p hp h1 h2 => Finset.disjoint_left.mp (hd (ne_of_mem_erase hk).symm)
        (Nat.mem_factoredNumbers'.mp (v i).property p hp h1)
        (Nat.mem_factoredNumbers'.mp (z k).property p hp h2)
    apply hcop.dvd_of_dvd_mul_right
    rw [mul_prod_erase univ (fun k => (z k).val) (mem_univ i), ← he]
    exact dvd_prod_of_mem _ (mem_univ i)
  exact funext fun i => Subtype.ext (Nat.dvd_antisymm (dvd x y he i) (dvd y x he.symm i))

omit [Fintype ι] in
lemma P_biUnion (s : Finset ι) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    P (s.biUnion A) = ∏ i ∈ s, P (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [P]
  | insert i s hi ih =>
    rw [biUnion_insert,prod_insert hi,P_union _,ih]
    exact disjoint_left.mpr fun p hp hh => by
      obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hh
      exact disjoint_left.mp (hd (by rintro rfl; contradiction)) hp hpk

theorem product_law (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (Measure.pi fun i => law (A i)).map (join A) = law (univ.biUnion A) := by
  classical
  let μ := Measure.pi fun i => law (A i)
  let ν := law (univ.biUnion A)
  have hmeas : Measurable (join A) := measurable_of_countable _
  have : IsProbabilityMeasure (μ.map (join A)) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have atom_eq (x : ∀ i, Integers (A i)) : μ {x} = ν {join A x} := by
    rw [Measure.pi_singleton,law_atom]
    simp only [law_atom]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg (x i))]
    congr 1
    simp [harmonic, join, P_biUnion A _ hd,prod_div_distrib,prod_inv_distrib]
  change μ.map (join A) = ν
  apply Measure.eq_of_le_of_measure_univ_eq _ (by simp [ν])
  apply Measure.le_iff.mpr
  intro s hs
  rw [← Measure.tsum_indicator_apply_singleton (μ.map (join A)) s hs, ← Measure.tsum_indicator_apply_singleton ν s hs]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    by_cases hx : ∃ x, join A x = a
    · obtain ⟨x,rfl⟩ := hx
      have hpre : (join A) ⁻¹' {join A x} = {x} := by
        ext y; exact (join_injective A hd).eq_iff
      rw [hpre]
      exact (atom_eq x).le
    · have hem : (join A) ⁻¹' {a} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hh => hx ⟨x,hh⟩
      simp [hem]
  · simp [ha]

#print axioms product_law
end Shift490

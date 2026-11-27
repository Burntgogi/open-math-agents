import Cofactor
namespace Erdos490Transfer
open Finset
noncomputable section
open Classical

/-- Maximum clique in the graph of allowed quotients on the prefix. For the
blue side the allowed quotients are the complement inside the finite ratio set. -/
def choices (U : Finset ℕ) (G : Finset ℚ) (t : ℕ) :=
  ((U.filter (· ≤ t)).powerset).filter (fun S => ratios S ⊆ G)
lemma mem_choices {U G t S} : S ∈ choices U G t ↔
    (∀ u ∈ S, u ∈ U ∧ u ≤ t) ∧ ratios S ⊆ G := by
  simp only [choices,mem_filter,mem_powerset,subset_iff,mem_filter]
lemma has_best (U G t) : ∃ S ∈ choices U G t, ∀ T ∈ choices U G t, T.card ≤ S.card := by
  apply exists_max_image
  refine ⟨∅,mem_choices.mpr ⟨by simp,by simp [ratios]⟩⟩

def best (U G t) := (has_best U G t).choose
theorem best_mem (U G t) : best U G t ∈ choices U G t := (has_best U G t).choose_spec.1
def rank (U G t) := (best U G t).card
lemma le_rank {U G t S} (h : S ∈ choices U G t) : S.card ≤ rank U G t :=
  (has_best U G t).choose_spec.2 _ h
lemma rank_mono (U G) : Monotone (rank U G) := by
  intro a b hab
  apply le_rank
  obtain ⟨hp,hr⟩ := mem_choices.mp (best_mem U G a)
  exact mem_choices.mpr ⟨fun u hu => ⟨(hp u hu).1,(hp u hu).2.trans hab⟩,hr⟩
lemma rank_zero {U} (hU : 0 ∉ U) (G) : rank U G 0 = 0 := by
  rw [rank,card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hm,hl⟩ := (mem_choices.mp (best_mem U G 0)).1 u hu
  exact hU (Nat.eq_zero_of_le_zero hl ▸ hm)
def weight (U G) (i : ℕ) := rank U G (i+1) - rank U G i

lemma rank_step (U G i) : rank U G (i+1) = rank U G i + weight U G i := by
  have : rank U G i ≤ rank U G (i+1) := rank_mono U G (Nat.le_succ i)
  unfold weight
  omega

lemma weight_le_one (U G i) : weight U G i ≤ 1 := by
  let S := best U G (i+1)
  obtain ⟨hp,hr⟩ := mem_choices.mp (best_mem U G (i+1))
  have hh : S.erase (i+1) ∈ choices U G i := by
    refine mem_choices.mpr ⟨?_,(ratios_mono (erase_subset ..)).trans hr⟩
    intro u hu
    obtain ⟨hne,hm⟩ := mem_erase.mp hu
    obtain ⟨hU,hl⟩ := hp u hm
    exact ⟨hU,by omega⟩
  have hh' := le_rank hh
  have he : S.card ≤ (S.erase (i+1)).card + 1 := by
    by_cases hm : i+1 ∈ S
    · rw [card_erase_add_one hm]
    · simp [erase_eq_of_notMem hm]
  change S.card - rank U G i ≤ 1
  omega

lemma rank_sum {U} (hU : 0 ∉ U) (G t K) :
    rank U G (min K t) = ∑ i ∈ range K, if i+1 ≤ t then weight U G i else 0 := by
  induction K with
  | zero => simp [rank_zero hU]
  | succ k ih =>
    rw [sum_range_succ,← ih]
    by_cases h : k+1 ≤ t
    · rw [if_pos h,min_eq_left h,min_eq_left (by omega)]
      exact rank_step U G k
    · rw [if_neg h,min_eq_right (by omega),min_eq_right (by omega),add_zero]

def size (U G C K n) := ∑ i ∈ range K, weight U G i * (semigroup C (n/(i+1))).card

lemma prefix_count {U} (hU : 0 ∉ U) (G C K n) :
    (∑ h ∈ semigroup C n, rank U G (min K (n/h))) = size U G C K n := by
  simp_rw [rank_sum hU]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have filt : (semigroup C n).filter (fun h => h ≤ n/(i+1)) = semigroup C (n/(i+1)) := by
    ext h
    simp only [mem_filter,mem_semigroup]
    constructor
    · exact fun x => ⟨x.1.1,x.2⟩
    · exact fun x => ⟨⟨x.1,x.2.trans (Nat.div_le_self ..)⟩,x.2⟩
  calc
    _ = ∑ h ∈ semigroup C n, if h ≤ n/(i+1) then weight U G i else 0 := by
      apply sum_congr rfl
      intro h hh
      simp only [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1),
        Nat.le_div_iff_mul_le (Nat.zero_lt_succ i),mul_comm (i+1) h]
    _ = _ := by rw [← sum_filter, filt]; simp [mul_comm]

lemma zero_not_vertex (Y K) : 0 ∉ vertices Y K := fun h => (mem_semigroup.mp h).1.1 rfl

/-- Flatten the independently selected fibers into a set of integers. -/
def assemble (H : Finset ℕ) (F : ℕ → Finset ℕ) :=
  (H.sigma F).image (fun x => x.1 * x.2)
lemma mem_assemble {H F z} : z ∈ assemble H F ↔ ∃ h ∈ H, ∃ u ∈ F h, h*u=z := by
  simp only [assemble,mem_image,Sigma.exists,mem_sigma]
  constructor
  · rintro ⟨h,u,⟨hh,hu⟩,he⟩
    exact ⟨h,hh,u,hu,he⟩
  · rintro ⟨h,hh,u,hu,he⟩
    exact ⟨h,u,⟨hh,hu⟩,he⟩

lemma assemble_card {C n Y K F} (hd : Disjoint C Y.primesBelow)
    (hf : ∀ h ∈ semigroup C n, F h ⊆ vertices Y K) :
    (assemble (semigroup C n) F).card = ∑ h ∈ semigroup C n, (F h).card := by
  rw [assemble,card_image_of_injOn,card_sigma]
  rintro ⟨h,u⟩ hx ⟨j,v⟩ hy eq
  obtain ⟨hh,hu⟩ := mem_sigma.mp hx
  obtain ⟨hj,hv⟩ := mem_sigma.mp hy
  change h*u=j*v at eq
  obtain rfl := recover (coprime_active hd (mem_semigroup.mp hh).1 (mem_semigroup.mp (hf _ hj hv)).1)
    (coprime_active hd (mem_semigroup.mp hj).1 (mem_semigroup.mp (hf _ hh hu)).1) eq
  obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1) eq
  rfl

end
end Erdos490Transfer

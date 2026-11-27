import Weights
namespace Erdos490Transfer
open Finset
noncomputable section
open Classical

lemma old_size {Y K n C A G} (cover : Covers Y K n C A) (bound : A ⊆ Icc 1 n)
    (hd : Disjoint C Y.primesBelow)
    (graph : ∀ h ∈ semigroup C n, ratios (fiber (vertices Y K) A h) ⊆ G) :
    A.card ≤ size (vertices Y K) G C K n := by
  let U := vertices Y K
  let F := fiber U A
  have sub : A ⊆ assemble (semigroup C n) F := by
    intro z hz
    obtain ⟨h,hh,u,hu,he⟩ := cover _ hz
    exact mem_assemble.mpr ⟨h,hh,u,mem_filter.mpr ⟨hu,he ▸ hz⟩,he⟩
  apply (card_le_card sub).trans
  rw [assemble_card (F:=F) (K:=K) hd (fun _ _ => filter_subset ..),← prefix_count (zero_not_vertex Y K)]
  apply sum_le_sum
  intro h hh
  refine le_rank (mem_choices.mpr ⟨?_,graph _ hh⟩)
  intro u hu
  obtain ⟨hu',ha⟩ := mem_filter.mp hu
  exact ⟨hu',le_min (mem_semigroup.mp hu').2
    ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1)).mpr
    (mul_comm u h ▸ (mem_Icc.mp (bound ha)).2))⟩

/-- Every admissible pair in the specified coloring is bounded on both sides
by the same graph and its complement. -/
theorem dominate {Y K n A B} (ha : Adm n A B) (c : Colors Y n)
    (ca : Covers Y K n c.red A) (cb : Covers Y K n c.blue B) :
    ∃ G ⊆ ratios (vertices Y K),
      A.card ≤ size (vertices Y K) G c.red K n ∧
      B.card ≤ size (vertices Y K) (ratios (vertices Y K) \ G) c.blue K n := by
  let U := vertices Y K
  refine ⟨oldGraph U (semigroup c.red n) A,oldGraph_subset ..,
    old_size ca ha.1 c.small_disjoint.1 (fun _ hh => subset_biUnion_of_mem (fun h => ratios (fiber U A h)) hh),
    old_size cb ha.2.1 c.small_disjoint.2 ?_⟩
  intro h hh q hq
  exact mem_sdiff.mpr ⟨ratios_mono (filter_subset ..) hq,disjoint_left.mp (old_blue ha c hh) hq⟩

def optimal (Y K n : ℕ) (G : Finset ℚ) (C : Finset ℕ) :=
  assemble (semigroup C n) (fun h => best (vertices Y K) G (min K (n/h)))

lemma optimal_data {Y K n G C z} (hz : z ∈ optimal Y K n G C) :
    ∃ h ∈ semigroup C n, ∃ u ∈ best (vertices Y K) G (min K (n/h)),
      u ∈ vertices Y K ∧ h*u=z ∧ z ∈ Icc 1 n := by
  obtain ⟨h,hh,u,hu,rfl⟩ := mem_assemble.mp hz
  obtain ⟨hm,hl⟩ := (mem_choices.mp (best_mem ..)).1 u hu
  have hpos := Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1
  refine ⟨h,hh,u,hu,hm,rfl,mem_Icc.mpr ⟨Nat.mul_pos hpos
    (Nat.pos_of_ne_zero (mem_semigroup.mp hm).1.1),?_⟩⟩
  rw [mul_comm]
  exact (Nat.le_div_iff_mul_le hpos).mp (hl.trans (min_le_right ..))

theorem optimal_card {Y K n G C} (hd : Disjoint C Y.primesBelow) :
    (optimal Y K n G C).card = size (vertices Y K) G C K n := by
  rw [optimal,assemble_card hd,← prefix_count (zero_not_vertex Y K)]
  · rfl
  · exact fun h _ u hu => ((mem_choices.mp (best_mem ..)).1 u hu).1

/-- Project a product onto both disjoint sets of large primes. -/
lemma recover_rough {Y n} (c : Colors Y n) {h j k l u v x y : ℕ}
    (hh : Active c.red h) (hj : Active c.blue j) (hk : Active c.red k) (hl : Active c.blue l)
    (hu : Active Y.primesBelow u) (hv : Active Y.primesBelow v)
    (hx : Active Y.primesBelow x) (hy : Active Y.primesBelow y)
    (he : (h*u)*(j*v)=(k*x)*(l*y)) : h=k ∧ j=l ∧ u*v=x*y := by
  have huv := Nat.mul_mem_factoredNumbers hu hv
  have hxy := Nat.mul_mem_factoredNumbers hx hy
  have eq : h*(j*(u*v))=k*(l*(x*y)) := by linear_combination (norm := ring) he
  have e := recover ((coprime_active c.separate hh hl).mul_right
    (coprime_active c.small_disjoint.1 hh hxy)) ((coprime_active c.separate hk hj).mul_right
    (coprime_active c.small_disjoint.1 hk huv)) eq
  subst k
  have eq' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh.1) eq
  have e := recover (coprime_active c.small_disjoint.2 hj hxy) (coprime_active c.small_disjoint.2 hl huv) eq'
  subst l
  exact ⟨rfl,rfl,Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj.1) eq'⟩

lemma cofactor_injective {S T : Finset ℕ} (hs : 0 ∉ S) (ht : 0 ∉ T)
    (hg : Disjoint (ratios S) (ratios T)) {u v x y : ℕ}
    (hu : u ∈ S) (hv : v ∈ T) (hx : x ∈ S) (hy : y ∈ T) (he : u*v=x*y) :
    u=x ∧ v=y := by
  have excl {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T)
      (hl : a < b) (e : a*d=b*c) : False := by
    have a0 : a ≠ 0 := fun h => hs (h ▸ ha)
    have c0 : c ≠ 0 := fun h => ht (h ▸ hc)
    have hlt : c < d := by
      by_contra! h
      exact (Nat.mul_lt_mul_of_pos_right hl (Nat.pos_of_ne_zero c0)).not_ge
        (e ▸ Nat.mul_le_mul_left a h)
    have eq := (ratio_eq a0 c0).mpr (show b*c=d*a by rw [← e,mul_comm])
    exact disjoint_left.mp hg (mem_ratios.mpr ⟨a,ha,b,hb,hl,rfl⟩)
      (mem_ratios.mpr ⟨c,hc,d,hd,hlt,eq.symm⟩)
  have eq : u=x := by
    rcases lt_trichotomy u x with hl|eq|hl
    · exact (excl hu hx hy hv hl he).elim
    · exact eq
    · exact (excl hx hu hv hy hl he.symm).elim
  subst x
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (fun e => hs (e ▸ hu))) he⟩

theorem attainable {Y K n} (c : Colors Y n) (G : Finset ℚ) :
    let U := vertices Y K
    let A := optimal Y K n G c.red
    let B := optimal Y K n (ratios U \ G) c.blue
    Adm n A B ∧ Covers Y K n c.red A ∧ Covers Y K n c.blue B ∧
      A.card = size U G c.red K n ∧ B.card = size U (ratios U \ G) c.blue K n := by
  dsimp only
  have bound {D H} : optimal Y K n H D ⊆ Icc 1 n := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,hb⟩ := optimal_data hz
    exact hb
  have cover {D H} : Covers Y K n D (optimal Y K n H D) := by
    intro z hz
    obtain ⟨h,hh,u,_,hu,he,_⟩ := optimal_data hz
    exact ⟨h,hh,u,hu,he⟩
  refine ⟨⟨bound,bound,?_⟩,cover,cover,optimal_card c.small_disjoint.1,optimal_card c.small_disjoint.2⟩
  intro a ha b hb a' ha' b' hb' he
  obtain ⟨h,hh,u,hu,hu',rfl,_⟩ := optimal_data ha
  obtain ⟨j,hj,v,hv,hv',rfl,_⟩ := optimal_data hb
  obtain ⟨k,hk,x,hx,hx',rfl,_⟩ := optimal_data ha'
  obtain ⟨l,hl,y,hy,hy',rfl,_⟩ := optimal_data hb'
  obtain ⟨rfl,rfl,eq⟩ := recover_rough c (mem_semigroup.mp hh).1 (mem_semigroup.mp hj).1
    (mem_semigroup.mp hk).1 (mem_semigroup.mp hl).1 (mem_semigroup.mp hu').1
    (mem_semigroup.mp hv').1 (mem_semigroup.mp hx').1 (mem_semigroup.mp hy').1 he
  have nz {D t} : 0 ∉ best (vertices Y K) D t :=
    fun h => zero_not_vertex Y K (((mem_choices.mp (best_mem ..)).1 _ h).1)
  obtain ⟨rfl,rfl⟩ := cofactor_injective nz nz (disjoint_left.mpr (fun _ hq hr =>
    (mem_sdiff.mp ((mem_choices.mp (best_mem ..)).2 hr)).2 ((mem_choices.mp (best_mem ..)).2 hq)))
    hu hv hx hy eq
  exact ⟨rfl,rfl⟩

end
end Erdos490Transfer

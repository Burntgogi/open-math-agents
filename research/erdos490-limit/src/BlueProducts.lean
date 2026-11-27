import TransplantColors
import StableTransfer

/-! Simultaneous lower counts for a family of old supports. The old support
is recovered from each new high product, even across different word lengths. -/
namespace Erdos490Transfer
open Finset Filter Real
noncomputable section
open Classical

theorem newProducts_recognize {b t : ℝ} (ht : 0 ≤ t) {S : Finset ℕ} {z : ℕ}
    (hz : z ∈ newProducts b t S) (p : ℕ) :
    p ∈ S ↔ ∃ q ∈ newCell b t p, q ∣ z := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  have selected : ∀ j : S, f j ∈ newCell b t j.val := Fintype.mem_piFinset.mp hf
  constructor
  · intro hp
    let i : S := ⟨p,hp⟩
    have dv : f i ∣ high f := dvd_prod_of_mem f (mem_univ i)
    exact ⟨f i,selected i,dv⟩
  · rintro ⟨q,hq,hd⟩
    have hprime : Nat.Prime q := (mem_filter.mp hq).2
    obtain ⟨j,_,hj⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hd
    have hq' := selected j
    have he := (Nat.prime_dvd_prime_iff_eq hprime (mem_filter.mp hq').2).mp hj
    have hp : p=j.val := by
      by_contra h
      exact disjoint_left.mp (newCell_disjoint ht h) hq (he ▸ hq')
    exact hp ▸ j.property

theorem products_apart {b t : ℝ} (ht : 0 ≤ t) {S T : Finset ℕ} (h : S ≠ T) :
    Disjoint (newProducts b t S) (newProducts b t T) := by
  apply disjoint_left.mpr
  intro z hs hr
  exact h (Finset.ext (fun p => (newProducts_recognize ht hs p).trans (newProducts_recognize ht hr p).symm))

lemma newProduct_active {b t : ℝ} {C S : Finset ℕ} (hs : S ⊆ C) {z : ℕ}
    (hz : z ∈ newProducts b t S) : Active (bands b t C) z := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  apply high_active (cell:=fun i : S => newCell b t i)
    (fun _ _ h => (mem_filter.mp h).2) (fun i _ h => mem_biUnion.mpr ⟨i.val,hs i.property,h⟩)
  exact fun i => Or.inr (Fintype.mem_piFinset.mp hf i)

lemma in_newCell {b t : ℝ} (ht : 0 < t) {p q : ℕ} (h : q ∈ newCell b t p) :
    Erdos490PrimeCells.boundary b p < log q/t ∧ log q/t ≤ Erdos490PrimeCells.boundary b (p+1) := by
  have hp := (mem_filter.mp h).2.pos
  have hh := mem_Ioc.mp (mem_filter.mp h).1
  have hq : 0 < (q:ℝ) := by exact_mod_cast hp
  constructor
  · rw [lt_div_iff₀ ht,mul_comm]
    exact (lt_log_iff_exp_lt hq).mpr ((Nat.floor_lt (exp_pos _).le).mp hh.1)
  · rw [div_le_iff₀ ht,mul_comm]
    exact (log_le_iff_le_exp hq).mpr ((Nat.le_floor_iff (exp_pos _).le).mp hh.2)

theorem newProduct_displacement {b t : ℝ} (ht : 0 < t) {S : Finset ℕ}
    (hp : ∀ p ∈ S, p.Prime) (e : ℕ → ℝ) (hc : ∀ p ∈ S, ∀ v ∈ Set.Ioc (Erdos490PrimeCells.boundary b p)
      (Erdos490PrimeCells.boundary b (p+1)), |v-log p| ≤ e p)
    {z : ℕ} (hz : z ∈ newProducts b t S) :
    |log z/t-log (∏ p ∈ S, p:ℕ)| ≤ ∑ p ∈ S, e p := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  have hq (i : S) := Fintype.mem_piFinset.mp hf i
  have id1 : log ((high f:ℕ):ℝ) = ∑ i : S, log (f i) := by
    rw [high,Nat.cast_prod,log_prod (fun i _ => by exact_mod_cast (mem_filter.mp (hq i)).2.ne_zero)]
  have id2 : log ((∏ p ∈ S, p:ℕ):ℝ) = ∑ p ∈ S, log p := by
    rw [Nat.cast_prod,log_prod (fun p h => by exact_mod_cast (hp p h).ne_zero)]
  rw [id1,id2,sum_div,← sum_attach S (fun p : ℕ => log (p:ℝ)),← sum_attach S e,attach_eq_univ,← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => hc i.val i.property _ (in_newCell ht (hq i))))

private lemma residual_count {D U A : Finset ℕ} (sep : Disjoint D U)
    (ha : ∀ z ∈ A, Active D z) (N : ℕ) :
    (∑ z ∈ A, (semigroup U (N/z)).card) ≤ (semigroup (D ∪ U) N).card := by
  let V := A.sigma (fun z => semigroup U (N/z))
  let f (w : Sigma (fun _ : ℕ => ℕ)) := w.1*w.2
  have hinj : Set.InjOn f V := by
    rintro ⟨z,v⟩ hv ⟨w,r⟩ hr eq
    obtain ⟨hz,hv⟩ := mem_sigma.mp hv
    obtain ⟨hw,hr⟩ := mem_sigma.mp hr
    change z*v=w*r at eq
    obtain rfl := recover (coprime_active sep (ha _ hz) (mem_semigroup.mp hr).1)
      (coprime_active sep (ha _ hw) (mem_semigroup.mp hv).1) eq
    obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (ha _ hz).1) eq
    rfl
  have sub : V.image f ⊆ semigroup (D ∪ U) N := by
    intro z hz
    obtain ⟨⟨w,v⟩,h,rfl⟩ := mem_image.mp hz
    obtain ⟨hw,hv⟩ := mem_sigma.mp h
    obtain ⟨hact,hcut⟩ := mem_semigroup.mp hv
    exact mem_semigroup.mpr ⟨Nat.mul_mem_factoredNumbers
      (Nat.factoredNumbers_mono subset_union_left (ha _ hw))
      (Nat.factoredNumbers_mono subset_union_right hact),by
      simpa [f,mul_comm] using (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (ha _ hw).1)).mp hcut⟩
  simpa [card_image_of_injOn hinj,V,card_sigma] using card_le_card sub

/-- Sum all old supports simultaneously. Every residual count has the
prescribed integer cutoff, and no product can be counted in two fibers. -/
theorem family_density_lower {b t : ℝ} (ht : 0 ≤ t) (C U : Finset ℕ)
    (sep : Disjoint (bands b t C) U) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C)
    (n u : ℕ) :
    (∑ S ∈ G, ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹*density U n (u*z)) ≤
      density (bands b t C ∪ U) n u := by
  let A := G.biUnion (newProducts b t)
  have apart : (G:Set (Finset ℕ)).PairwiseDisjoint (newProducts b t) :=
    fun _ _ _ _ h => products_apart ht h
  have active : ∀ z ∈ A, Active (bands b t C) z := by
    intro z h
    obtain ⟨S,hS,hz⟩ := mem_biUnion.mp h
    exact newProduct_active (hG _ hS) hz
  rw [← sum_biUnion apart]
  calc
    _ = (∑ z ∈ A, ((semigroup U (n/u/z)).card:ℝ))*u/n := by
      rw [sum_mul,sum_div]; apply sum_congr rfl; intro z hz
      have h0 : (z:ℝ) ≠ 0 := by exact_mod_cast (active z hz).1
      unfold density
      rw [Nat.div_div_eq_div_mul,Nat.cast_mul]
      by_cases hn : n=0
      · simp [hn]
      field_simp
    _ ≤ _ := by
      unfold density
      gcongr
      exact_mod_cast residual_count sep active (n/u)

#print axioms family_density_lower
#print axioms newProduct_displacement
end
end Erdos490Transfer

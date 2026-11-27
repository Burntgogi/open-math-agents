import PrimeColorTransfer
import MertensBounds

/-! Comparison between truncated harmonic normalization and the Euler
normalization in the analytic notes. All constants are uniform in the color. -/
namespace Erdos490Transfer
open Finset Filter
noncomputable section
open Classical

def euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
def truncMass (C : Finset ℕ) (n : ℕ) : ℝ := ∑ h ∈ semigroup C n, (h:ℝ)⁻¹

lemma truncMass_nonneg (C n) : 0 ≤ truncMass C n := sum_nonneg (fun _ _ => by positivity)

lemma euler_pos {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) : 0 < euler C := by
  apply prod_pos
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (hC p hp).one_lt
  exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ h))

lemma truncMass_le_euler {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) (n : ℕ) :
    truncMass C n ≤ euler C := by
  let f : ℕ →* ℝ := { toFun := fun t => (t:ℝ)⁻¹, map_one' := by simp, map_mul' := by simp [mul_comm] }
  have h (p : ℕ) (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have he := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=f) (fun {p} hp => h p hp) C).2
  rw [filter_true_of_mem hC] at he
  let s := semigroup C n
  let g (x : {h // h ∈ s}) : Nat.factoredNumbers C := ⟨x.1,(mem_semigroup.mp x.2).1⟩
  have hi : Function.Injective g := fun _ _ e => Subtype.ext (congrArg (fun t : Nat.factoredNumbers C => (t:ℕ)) e)
  have hs := sum_le_hasSum (s.attach.image g) (fun (x : Nat.factoredNumbers C) _ =>
    show 0 ≤ f x.val by dsimp [f]; positivity) he
  rw [sum_image (fun _ _ _ _ => @hi _ _)] at hs
  change (∑ x ∈ s.attach, ((x.val:ℕ):ℝ)⁻¹) ≤ euler C at hs
  rw [sum_attach s (fun x : ℕ => (x:ℝ)⁻¹)] at hs
  exact hs

lemma active_split (C D : Finset ℕ) (z : ℕ) (hz : Active (C ∪ D) z) :
    ∃ a b : ℕ, Active C a ∧ Active D b ∧ a*b=z := by
  induction z using Nat.recOnMul with
  | zero => exact (hz.1 rfl).elim
  | one => exact ⟨1,1,by simp [Active,Nat.mem_factoredNumbers],by simp [Active,Nat.mem_factoredNumbers],rfl⟩
  | prime p hp =>
    have h := Nat.mem_factoredNumbers'.mp hz p hp dvd_rfl
    have act {S : Finset ℕ} (hs : p ∈ S) : Active S p := by
      simpa [Active,Nat.mem_factoredNumbers,Nat.primeFactorsList_prime hp,hp.ne_zero] using hs
    rcases mem_union.mp h with h|h
    · exact ⟨p,1,act h,by simp [Active,Nat.mem_factoredNumbers],mul_one _⟩
    · exact ⟨1,p,by simp [Active,Nat.mem_factoredNumbers],act h,one_mul _⟩
  | mul a b ia ib =>
    obtain ⟨x,y,hx,hy,ex⟩ := ia (Nat.mem_factoredNumbers_of_dvd hz (dvd_mul_right ..))
    obtain ⟨u,v,hu,hv,ev⟩ := ib (Nat.mem_factoredNumbers_of_dvd hz (dvd_mul_left ..))
    exact ⟨x*u,y*v,Nat.mul_mem_factoredNumbers hx hu,Nat.mul_mem_factoredNumbers hy hv,by rw [← ex,← ev]; ring⟩

/-- Dropping a color can only increase the fraction of the harmonic Euler
mass retained up to n. The unrestricted harmonic sum is bounded by the two
truncated sums, by splitting each positive integer into its colored parts. -/
lemma harmonic_le_product {C D : Finset ℕ} {n : ℕ} (hcd : C ∪ D = n.primesLE) :
    (harmonic n:ℝ) ≤ truncMass C n * truncMass D n := by
  let S := semigroup C n ×ˢ semigroup D n
  let f (t : ℕ × ℕ) := t.1*t.2
  have covers : Icc 1 n ⊆ S.image f := by
    intro z hz
    obtain ⟨hz0,hzn⟩ := mem_Icc.mp hz
    have act : Active (C ∪ D) z := Nat.mem_factoredNumbers'.mpr (fun p hp hd => by
      rw [hcd]; exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hz0 hd).trans hzn,hp⟩)
    obtain ⟨a,b,ha,hb,he⟩ := active_split C D z act
    refine mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_semigroup.mpr ⟨ha,?_⟩,mem_semigroup.mpr ⟨hb,?_⟩⟩,he⟩
    · exact (Nat.le_of_dvd hz0 (he ▸ dvd_mul_right a b)).trans hzn
    · exact (Nat.le_of_dvd hz0 (he ▸ dvd_mul_left b a)).trans hzn
  calc
    _ = ∑ h ∈ Icc 1 n, (h:ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
    _ ≤ ∑ h ∈ S.image f, (h:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg covers (fun _ _ _ => by positivity)
    _ ≤ ∑ t ∈ S, ((f t:ℕ):ℝ)⁻¹ := sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = _ := by simp [S,f,truncMass,sum_mul_sum,sum_product,mul_comm]

/-- Only an order bound in Mertens' theorem is needed for this conversion. -/
theorem euler_le_trunc_uniform : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ C ⊆ n.primesLE, euler C ≤ B*truncMass C n := by
  obtain ⟨c,hc,hm⟩ := mertens_product_lower
  refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
  intro n hn C hC
  let D := n.primesLE \ C
  have hD : ∀ p ∈ D, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2
  have hCp : ∀ p ∈ C, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (hC hp)).2
  have hall : C ∪ D = n.primesLE := by ext p; simp [D]; grind
  have hd : Disjoint C D := disjoint_left.mpr (fun {_} h h' => (mem_sdiff.mp h').2 h)
  have prod : euler C*euler D=euler n.primesLE := by
    unfold euler
    rw [← prod_union hd,hall]
  have n2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlow := hm n hn
  have hfull : euler n.primesLE ≤ (Real.log n)/c := by
    unfold euler
    rw [prod_inv_distrib]
    simp only [one_div] at hlow
    have hp : 0 < ∏ p ∈ n.primesLE, (1-(p:ℝ)⁻¹) := (div_pos hc hl).trans_le hlow
    rw [inv_le_comm₀ hp (div_pos hl hc)]
    simpa using hlow
  have hlog : Real.log (n:ℝ) ≤ (harmonic n:ℝ) := by
    simpa using log_le_harmonic_floor (n:ℝ) (by positivity)
  have hmass := (hlog.trans (harmonic_le_product hall)).trans
    (mul_le_mul_of_nonneg_left (truncMass_le_euler hD n) (truncMass_nonneg C n))
  have hfull' : euler C*euler D ≤ c⁻¹*(truncMass C n*euler D) := by
    rw [prod]
    exact hfull.trans (by rw [div_eq_inv_mul]; gcongr)
  exact (le_of_mul_le_mul_right (by simpa only [mul_assoc] using hfull') (euler_pos hD))

end
end Erdos490Transfer

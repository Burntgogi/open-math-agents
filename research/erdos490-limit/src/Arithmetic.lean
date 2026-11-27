import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

noncomputable section
namespace Shift490
open Finset Filter
abbrev Integers := Nat.factoredNumbers

def P (S : Finset ℕ) : ℝ := ∏ p ∈ S with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹

theorem P_pos (S : Finset ℕ) : 0 < P S := by
  apply prod_pos
  intro p hp
  have h : 1 < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))

def reciprocal : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by simp [mul_comm]

theorem harmonic_sum (S : Finset ℕ) :
    HasSum (fun n : Integers S => ((n : ℕ) : ℝ)⁻¹) (P S) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocal) ?_ S).2
  intro p hp
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact (inv_lt_one₀ (by positivity)).mpr h

def harmonic (S : Finset ℕ) (n : Integers S) := ((n : ℕ) : ℝ)⁻¹ / P S

theorem harmonic_probability (S : Finset ℕ) : HasSum (harmonic S) 1 := by
  unfold harmonic
  simpa only [div_self (P_pos S).ne'] using (harmonic_sum S).div_const (P S)

abbrev logN {S : Finset ℕ} (n : Integers S) := Real.log (n : ℕ)
def atom {S : Finset ℕ} (w : ℝ) (n : Integers S) : ℝ :=
  if logN n ≤ w then Real.exp (-w) else 0
def F (S : Finset ℕ) (w : ℝ) : ℝ := ∑' n : Integers S, atom w n

lemma nat_pos {S} (n : Integers S) : 0 < ((n : ℕ) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero n.property.1

lemma atom_nonneg {S w} (n : Integers S) : 0 ≤ atom w n := by
  unfold atom
  split <;> positivity

lemma atom_le {S w} (n : Integers S) : atom w n ≤ ((n : ℕ) : ℝ)⁻¹ := by
  unfold atom logN
  split_ifs with h
  · rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (nat_pos n)]
    exact (Real.log_le_iff_le_exp (nat_pos n)).mp h
  · positivity

lemma summable_atom (S w) : Summable (@atom S w) :=
  Summable.of_nonneg_of_le atom_nonneg atom_le (harmonic_sum S).summable

def countSet (S : Finset ℕ) (w : ℝ) :=
  (range (⌊Real.exp w⌋₊ + 1)).filter (· ∈ Integers S)

theorem F_eq_card (S w) : F S w = Real.exp (-w) * (countSet S w).card := by
  classical
  let t := (countSet S w).subtype (· ∈ Integers S)
  have ht (n : Integers S) : n ∈ t ↔ logN n ≤ w := by
    simp [t, countSet, logN, Nat.le_floor_iff (Real.exp_pos w).le,
      Real.log_le_iff_le_exp (nat_pos n), n.property]
  rw [F, tsum_eq_sum (s := t) (fun n hn => by simp [atom, mt (ht n).mpr hn])]
  calc
    _ = ∑ _n ∈ t, Real.exp (-w) := sum_congr rfl fun n hn => if_pos ((ht n).mp hn)
    _ = _ := by
      have he : t.card = (countSet S w).card := by
        simp [t, Finset.card_subtype, Finset.filter_eq_self.mpr
          (show ∀ n ∈ countSet S w, n ∈ Integers S from fun n hn => (mem_filter.mp hn).2)]
      simp [he, mul_comm]

def multiply {A B : Finset ℕ} (x : Integers A × Integers B) : Integers (A ∪ B) :=
  ⟨x.1.val * x.2.val, Nat.mul_mem_factoredNumbers
    (Nat.factoredNumbers_mono subset_union_left x.1.property)
    (Nat.factoredNumbers_mono subset_union_right x.2.property)⟩

theorem multiply_bijective {A B : Finset ℕ} (hd : Disjoint A B) :
    Function.Bijective (@multiply A B) := by
  have cop (a : Integers A) (b : Integers B) : a.val.Coprime b.val :=
    Nat.coprime_of_dvd fun p hp ha hb => Finset.disjoint_left.mp hd
      (Nat.mem_factoredNumbers'.mp a.property p hp ha)
      (Nat.mem_factoredNumbers'.mp b.property p hp hb)
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have he : a.val * b.val = c.val * d.val := congrArg Subtype.val h
    have hac := (cop a d).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a.val b.val)
    have hca := (cop c b).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right c.val d.val)
    have h1 := Nat.dvd_antisymm hac hca
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero c.property.1) (h1 ▸ he)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro n
    let l := n.val.primeFactorsList
    have part := List.Perm.prod_eq (List.filter_append_perm (fun p => decide (p ∈ A)) l)
    rw [List.prod_append, Nat.prod_primeFactorsList n.property.1] at part
    have other : l.filter (fun x => !decide (x ∈ A)) = l.filter (· ∈ B) := by
      apply List.filter_congr
      intro p hp
      have := mem_union.mp (n.property.2 p hp)
      have hd' : p ∈ A → p ∉ B := fun ha => Finset.disjoint_left.mp hd ha
      grind
    rw [other] at part
    exact ⟨(⟨_, Nat.prod_mem_factoredNumbers A n.val⟩,
      ⟨_, Nat.prod_mem_factoredNumbers B n.val⟩), Subtype.ext part⟩

theorem normalized_convolution {A B : Finset ℕ} (hd : Disjoint A B) (w : ℝ) :
    F (A ∪ B) w = P A * ∑' a : Integers A, harmonic A a * F B (w - logN a) := by
  let e := Equiv.ofBijective _ (multiply_bijective hd)
  have hs : Summable (fun x => atom w (e x)) := (e.summable_iff).mpr (summable_atom (A ∪ B) w)
  rw [F, ← e.tsum_eq, hs.tsum_prod, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [← mul_assoc, harmonic, mul_comm (P A), div_mul_cancel₀ _ (P_pos A).ne', F, ← tsum_mul_left]
  apply tsum_congr
  intro b
  change (if Real.log ((a.val * b.val : ℕ) : ℝ) ≤ w then _ else _) = _
  simp only [Nat.cast_mul, Real.log_mul (nat_pos a).ne' (nat_pos b).ne', atom, logN]
  simp only [show Real.log (a : ℕ) + Real.log (b : ℕ) ≤ w ↔ Real.log (b : ℕ) ≤ w - Real.log (a : ℕ) by constructor <;> intro h <;> linarith]
  by_cases h : Real.log (b : ℕ) ≤ w - Real.log (a : ℕ)
  · simp only [if_pos h]
    rw [show -(w - Real.log (a : ℕ)) = Real.log (a : ℕ) + (-w) by ring, Real.exp_add,
      Real.exp_log (nat_pos a), ← mul_assoc, inv_mul_cancel₀ (nat_pos a).ne', one_mul]
  · simp [h]

#print axioms harmonic_probability
#print axioms F_eq_card
#print axioms multiply_bijective
#print axioms normalized_convolution
end Shift490

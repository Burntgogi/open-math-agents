import AssemblyModel
import WitnessProbability

open Finset Real
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split OnePercent.Fourier

/-- An exponential generating-function bound counts *all* permitted sizes,
including the empty set. This spends two extra units in the intercept. -/
theorem count_subsets {α : Type*} [DecidableEq α] (P : Finset α)
    (B : Finset (Finset α)) {x a k : ℝ} (hx : 0 ≤ x)
    (hp : (P.card : ℝ) ≤ k * exp x)
    (hb : ∀ s ∈ B, s ⊆ P ∧ (s.card : ℝ) ≤ a) :
    (B.card : ℝ) ≤ exp (k + a*x) := by
  classical
  have hweight : ∑ s ∈ P.powerset, exp (-x * s.card) = (1 + exp (-x))^P.card := by
    have h := Finset.prod_one_add (f := fun _ : α => exp (-x)) P
    simp only [prod_const] at h
    simpa only [← Real.exp_nat_mul, mul_comm (-x)] using h.symm
  have hsum : (B.card : ℝ) * exp (-x*a) ≤ (1 + exp (-x)) ^ P.card := by
    rw [← hweight, ← nsmul_eq_mul, ← sum_const]
    refine (sum_le_sum (s := B) (g := fun s => exp (-x * (s.card:ℝ))) ?_).trans ?_
    · intro s hs
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hb s hs).2 (neg_nonpos.mpr hx))
    · exact sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (hb s hs).1)
        (fun _ _ _ => (exp_pos _).le)
  have hpow : (1 + exp (-x))^P.card ≤ exp k := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + exp (-x))
      (show 1 + exp (-x) ≤ exp (exp (-x)) by linarith only [Real.add_one_le_exp (exp (-x))]) P.card
    rw [← exp_nat_mul] at h
    apply h.trans (exp_le_exp.mpr ?_)
    calc
      (P.card : ℝ) * exp (-x) ≤ (k * exp x) * exp (-x) := mul_le_mul_of_nonneg_right hp (exp_pos _).le
      _ = k := by rw [exp_neg]; field_simp
  have h := mul_le_mul_of_nonneg_right (hsum.trans hpow) (exp_pos (a*x)).le
  rwa [mul_assoc, ← exp_add, show -x*a+a*x=0 by ring, exp_zero,mul_one,← exp_add] at h

theorem count_witnesses {C : Catalog p} (spec : StageSpec C) {i : ℕ} (hi : i < C.stages) :
    ((witnesses C i).card:ℝ) ≤
      ((C.containers i).card:ℝ) * (C.laws i).card *
        exp ((p.sqrt:ℝ)*(2+0.101*x p i)) := by
  classical
  let k := p.sqrt
  let y := x p i
  have hy : 0 ≤ y := le_trans (by norm_num) (spec.active i hi).le
  let f (P : Points p) := ((P.powersetCard (rSize k)) ×ˢ
    ((P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax k) ×ˢ C.laws i)).filter
    (fun w => FourierFit w.2.1 w.2.2 (7*eta y*w.2.1.card))
  have hsingle (P : Points p) (hP : P ∈ C.containers i) :
      ((f P).card:ℝ) ≤ (C.laws i).card * exp ((k:ℝ)*(2+0.101*y)) := by
    have hsize := spec.containerSize i hi.le P hP
    have hr := count_subsets P (P.powersetCard (rSize k)) (a := (0.1:ℝ)*k) hy hsize (by
      intro R hR
      obtain ⟨hsub,he⟩ := mem_powersetCard.mp hR
      have hh : (rSize k : ℝ)*10 ≤ k := by exact_mod_cast Nat.div_mul_le_self k 10
      exact ⟨hsub, by rw [he]; linarith⟩)
    have hs := count_subsets P (P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax k)
      (a := (0.001:ℝ)*k) hy hsize (by
        intro S hS
        obtain ⟨hsub,_,he⟩ := mem_filter.mp hS
        have hh : (sMax k : ℝ)*1000 ≤ k := by exact_mod_cast Nat.div_mul_le_self k 1000
        exact ⟨mem_powerset.mp hsub,(Nat.cast_le.mpr he).trans (by linarith)⟩)
    unfold f
    apply (Nat.cast_le.mpr (card_filter_le _ _)).trans
    rw [card_product,card_product,Nat.cast_mul,Nat.cast_mul,←mul_assoc]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hr hs (by positivity) (exp_pos _).le)
      (Nat.cast_nonneg _)).trans_eq
    rw [←exp_add,mul_comm]
    congr 2
    ring
  change (((C.containers i).biUnion f).card:ℝ) ≤ _
  refine (Nat.cast_le.mpr card_biUnion_le).trans ?_
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _ ∈ C.containers i, (C.laws i).card * exp ((k:ℝ)*(2+0.101*y)) := sum_le_sum hsingle
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

def hitBase (y : ℝ) := 2*(71000*eta y)^2
def hitBound (k : ℕ) (y : ℝ) := (2:ℝ)^k * hitBase y ^ ((0.24:ℝ)*k)

theorem base_bound {y : ℝ} : hitBase y ≤ exp (-1966 - 0.44*y) := by
  have he : (2:ℝ) ≤ exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hc : (2:ℝ)*71000^2 ≤ exp 34 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he 34
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  unfold hitBase eta
  rw [mul_pow, ←exp_nat_mul, ←mul_assoc]
  apply (mul_le_mul_of_nonneg_right hc (exp_pos _).le).trans_eq
  rw [←exp_add]
  congr 1
  push_cast
  ring

theorem paid_witnesses (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    exp ((k:ℝ)*(2+0.101*y)) * hitBound k y ≤ exp (-468*(k:ℝ)) := by
  have he : (2:ℝ) ≤ exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he k
  rw [← exp_nat_mul, mul_one] at h2
  have hq := Real.rpow_le_rpow (show 0 ≤ hitBase y by unfold hitBase; positivity)
    (base_bound (y:=y)) (show 0 ≤ (0.24:ℝ)*k by positivity)
  rw [←exp_mul] at hq
  unfold hitBound
  apply (mul_le_mul_of_nonneg_left (mul_le_mul h2 hq (Real.rpow_nonneg
    (by unfold hitBase; positivity) _) (exp_pos _).le) (exp_pos _).le).trans
  rw [←exp_add,←exp_add]
  apply exp_le_exp.mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) hy]

set_option maxHeartbeats 1200000 in
theorem witness_probability {C : Catalog p} (spec : StageSpec C) {i : ℕ} (hi : i < C.stages)
    (hk : 100000 ≤ p.sqrt) {w : W p} (hw : w ∈ witnesses C i) :
    probability (orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt)) (hits w) ≤
      hitBound p.sqrt (x p i) := by
  obtain ⟨P,_,hw⟩ := mem_biUnion.mp hw
  obtain ⟨hpair,hfit⟩ := mem_filter.mp hw
  have hr := (mem_powersetCard.mp (mem_product.mp hpair).1).2
  have hk0 : 0 < p.sqrt := by omega
  have hs : half p.sqrt + rest p.sqrt = p.sqrt := by dsimp [half,rest]; omega
  let D := fun A : Points p => exceptional (discrepancy (A+w.1) w.2.1 w.2.2)
    (cutoff w.1.card w.2.1.card p.sqrt)
  have hc : (univ : Points p).card = p := by simp
  have hb := witness_hits_probability (s := (univ : Points p)) (k₁ := half p.sqrt) (k₂ := rest p.sqrt)
    (η := eta (x p i)) (by rw [hs,hc]; exact Nat.sqrt_le_self _)
    (by rw [hc]; have h := Nat.sqrt_le_self p; dsimp [half]; omega)
    (by rw [hc]; exact Nat.pos_of_ne_zero (NeZero.ne p)) D
    (fun A _ => by
      rw [hc]
      refine exceptional_card_section5 (A+w.1) w.2.1 w.2.2 hk0 (exp_pos _).le ?_ hfit
      rw [hr,le_div_iff₀ (Nat.cast_pos.mpr hk0)]
      exact (mul_le_mul_of_nonneg_right (by norm_num : (0.099:ℝ) ≤ 0.0999) (Nat.cast_nonneg _)).trans
        (numerical (p:=p) hk (Nat.lt_succ_sqrt' p)).2.1)
    (by apply base_bound.trans; apply Real.exp_le_one_iff.mpr; linarith only [spec.active i hi])
  have heq : hits w = fun q => (0.24:ℝ)*p.sqrt ≤ (q.2 ∩ D q.1).card := rfl
  rw [heq]
  simpa only [hs,hitBound,hitBase] using hb

end
end Green39.Assembly
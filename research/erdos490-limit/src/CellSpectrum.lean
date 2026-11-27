import Selection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace Shift490
open Finset Real Filter
open scoped BigOperators

abbrev offset (j p : ℕ) : ℝ := log p-j

/-- A rectangular upper discrepancy for the entire prime cell suffices. The data are
uncolored. The mass lower bound is only needed for choosing one of the two sides. -/
def RectanglePNT (Y : ℕ) : Prop :=
  (∀ᶠ j : ℕ in atTop, 2/(3*(j:ℝ)) ≤ mass (cell Y j) ∧ mass (cell Y j) ≤ 1/2) ∧
  ∀ e : ℝ, 0 < e → ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, a ≤ b →
    (j:ℝ) * mass ((cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e

private lemma mono_mass {A B : Finset ℕ} (h : A ⊆ B) : mass A ≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)

private def radius (t : ℝ) := min 1 |t| / 1000
private def residue (x : ℝ) := x - (round (x/(2*π)) : ℝ)*(2*π)

private lemma residue_bound (x : ℝ) : |residue x| ≤ π := by
  have hp := Real.pi_pos
  have hr := mul_le_mul_of_nonneg_right (abs_sub_round (x/(2*π))) (show 0 ≤ 2*π by positivity)
  have ha : |x/(2*π)-(round (x/(2*π)):ℝ)| * (2*π) = |residue x| := by
    calc
      _ = |x/(2*π)-(round (x/(2*π)):ℝ)| * |2*π| := by rw [abs_of_pos (show 0 < 2*π by positivity)]
      _ = _ := by rw [← abs_mul,sub_mul,div_mul_cancel₀ _ (by positivity : 2*π ≠ 0)]; rfl
  rw [ha] at hr
  linarith

private lemma arc_small {Y j : ℕ} {e T : ℝ} (he : 0 < e)
    (heT : e*(2*T+9) ≤ 1/100)
    (hbox : ∀ a b : ℝ, a ≤ b → (j:ℝ)*mass ((cell Y j).filter
      (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e)
    (t α : ℝ) (ht : t ≠ 0) (hf : |t| ≤ T) (ha : |α| ≤ π) :
    (j:ℝ)*mass ((cell Y j).filter (fun p => |residue (t*offset j p-α)| ≤ radius t)) ≤ 1/6 := by
  classical
  let d := radius t / |t|
  have ht' := abs_pos.mpr ht
  have hr : 0 ≤ radius t := by dsimp [radius]; positivity
  have hd : 0 ≤ d := div_nonneg hr ht'.le
  let n : ℤ := ⌈|t|⌉+3
  let ks := Icc (-n) n
  let block (k : ℤ) := (cell Y j).filter (fun p =>
    (α+k*(2*π))/t - d ≤ offset j p ∧ offset j p ≤ (α+k*(2*π))/t + d)
  have sub : ((cell Y j).filter (fun p => |residue (t*offset j p-α)| ≤ radius t)) ⊆ ks.biUnion block := by
    intro p hp
    obtain ⟨hc,hres⟩ := mem_filter.mp hp
    let x := offset j p
    let k := round ((t*x-α)/(2*π))
    have hx : 0 ≤ x ∧ x ≤ 1 := by
      obtain ⟨h1,h2⟩ := (mem_filter.mp hc).2
      dsimp [x,offset]; constructor <;> linarith
    have hR : |t*x-α-k*(2*π)| ≤ π := residue_bound _
    have hdist : |t*x-α| ≤ |t|+π := by
      calc
        _ ≤ |t*x| + |α| := abs_sub _ _
        _ ≤ _ := by rw [abs_mul,abs_of_nonneg hx.1]; nlinarith [mul_nonneg ht'.le (sub_nonneg.mpr hx.2)]
    have hk : |(k:ℝ)| ≤ |t|+2 := by
      have h1 := abs_le.mp hR
      have h2 := abs_le.mp hdist
      have hπ := Real.pi_gt_three
      apply abs_le.mpr
      constructor <;> by_contra! h <;>
        nlinarith [mul_nonneg (show 0 ≤ 2*π-1 by linarith) ht'.le,
          mul_pos (sub_pos.mpr h) (show 0 < 2*π by positivity)]
    have hk' : k ∈ ks := by
      have hceil := Int.le_ceil |t|
      have h₁ : (-n:ℤ) ≤ k := by exact_mod_cast (show ((-n:ℤ):ℝ) ≤ k by dsimp [n]; push_cast; linarith [(abs_le.mp hk).1])
      have h₂ : k ≤ n := by exact_mod_cast (show (k:ℝ) ≤ (n:ℝ) by dsimp [n]; push_cast; linarith [(abs_le.mp hk).2])
      exact mem_Icc.mpr ⟨h₁,h₂⟩
    refine mem_biUnion.mpr ⟨k,hk',mem_filter.mpr ⟨hc,?_⟩⟩
    have hdx : |x-(α+k*(2*π))/t| ≤ d := by
      rw [show x-(α+k*(2*π))/t = (t*x-α-k*(2*π))/t by field_simp; ring,abs_div]
      exact div_le_div_of_nonneg_right hres ht'.le
    exact ⟨by linarith [(abs_le.mp hdx).1],by linarith [(abs_le.mp hdx).2]⟩
  have hcard : (ks.card:ℝ) ≤ 2*|t|+9 := by
    have hn : 0 ≤ n := by dsimp [n]; positivity
    simp only [ks,Int.card_Icc,sub_neg_eq_add]
    rw [show ((n+1+n).toNat:ℝ) = ((n+1+n:ℤ):ℝ) by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ n+1+n by omega)]
    push_cast
    dsimp [n]; push_cast
    linarith [Int.ceil_lt_add_one |t|]
  have hblock (k : ℤ) : (j:ℝ)*mass (block k) ≤ 2*d+e := by
    have hh := hbox ((α+k*(2*π))/t-d) ((α+k*(2*π))/t+d) (by linarith)
    dsimp [block]; linarith
  calc
    _ ≤ (j:ℝ)*mass (ks.biUnion block) := mul_le_mul_of_nonneg_left (mono_mass sub) (by positivity)
    _ ≤ (j:ℝ)*(∑ k ∈ ks, mass (block k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hb (u : Finset ℤ) : mass (u.biUnion block) ≤ ∑ k ∈ u, mass (block k) := by
        induction u using Finset.induction with
        | empty => simp [mass]
        | insert k u hk ih =>
          rw [biUnion_insert,sum_insert hk]
          have hi : mass (block k ∪ u.biUnion block) + mass (block k ∩ u.biUnion block) = mass (block k) + mass (u.biUnion block) := sum_union_inter
          have hn : 0 ≤ mass (block k ∩ u.biUnion block) := sum_nonneg fun _ _ => by positivity
          linarith
      exact hb ks
    _ ≤ ks.card * (2*d+e) := by
      rw [mul_sum]
      simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (s := ks) (fun k _ => hblock k)
    _ ≤ (2*|t|+9)*(2*d+e) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := by
      have hdt : d*|t| = radius t := div_mul_cancel₀ _ ht'.ne'
      have h1 : d ≤ 1/1000 := (div_le_iff₀ ht').mpr (by dsimp [radius]; linarith [min_le_right 1 |t|])
      have h2 : radius t ≤ 1/1000 := by dsimp [radius]; linarith [min_le_left 1 |t|]
      nlinarith [mul_nonneg he.le (sub_nonneg.mpr hf)]

private lemma cos_drop (x : ℝ) : 1 - cos x ≥ (residue x)^2 / 16 := by
  let y := residue x
  have hy : |y| ≤ π := residue_bound _
  have hs := Real.mul_le_sin (x := |y|/2) (by positivity) (by linarith)
  have hs' : |y|/4 ≤ sin (|y|/2) := by
    refine le_trans ?_ hs
    have hπ := Real.pi_lt_four
    field_simp
    nlinarith [mul_nonneg (abs_nonneg y) (show 0 ≤ 4-π by linarith)]
  have hc : cos x = 1 - 2*sin (|y|/2)^2 := by
    rw [← Real.cos_two_mul_eq_one_sub,show 2*(|y|/2)=|y| by ring,Real.cos_abs]
    exact (Real.cos_sub_int_mul_two_pi x _).symm
  rw [hc]
  nlinarith [sq_abs y,pow_le_pow_left₀ (show 0 ≤ |y|/4 by positivity) hs' 2]

private lemma rotate_char (A : Finset ℕ) (j : ℕ) (t : ℝ) (hmass : 0 < mass A) :
    mass A * ‖char A j t‖ = ∑ p ∈ A, (p:ℝ)⁻¹ * cos (t*offset j p - (char A j t).arg) := by
  let z := char A j t
  have harg := Complex.norm_mul_exp_arg_mul_I z
  have he : ((‖z‖ : ℝ):ℂ) = z * Complex.exp (-(z.arg * Complex.I)) := by
    calc
      _ = ((‖z‖:ℝ):ℂ) * (Complex.exp (z.arg * Complex.I) * Complex.exp (-(z.arg * Complex.I))) := by rw [← Complex.exp_add]; simp
      _ = _ := by rw [← mul_assoc,harg]
  have hm : (mass A:ℂ) * z = ∑ p ∈ A, (p:ℂ)⁻¹ * Complex.exp ((t*offset j p : ℝ)*Complex.I) := by
    dsimp only [z,char,offset]
    rw [mul_comm,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hmass.ne')]
  have hrot := congrArg Complex.re (show ((mass A:ℂ) * (‖z‖:ℝ)) =
      ∑ p ∈ A, (p:ℂ)⁻¹ * Complex.exp (((t*offset j p - z.arg:ℝ):ℂ)*Complex.I) by
    rw [he, ← mul_assoc,hm,sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [mul_assoc,← Complex.exp_add,Complex.ofReal_sub,sub_mul,sub_eq_add_neg])
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.re_sum,Complex.exp_ofReal_mul_I_re,← Complex.ofReal_natCast,← Complex.ofReal_inv] at hrot
  exact hrot

theorem prime_cells_of_rectangles {Y : ℕ} (pnt : RectanglePNT Y) : PrimeCellInput Y := by
  refine ⟨pnt.1, (1/32000000:ℝ),by norm_num,?_⟩
  intro m
  let T := max 1 ((m:ℝ)^2)
  let e := (1/100:ℝ)/(2*T+9)
  have hT : 1 ≤ T := le_max_left .. 
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [pnt.2 e he,eventually_gt_atTop 0] with j hbox hj A hA hd
  have hj' : 0 < (j:ℝ) := by exact_mod_cast hj
  have hmass : 0 < mass A := lt_of_lt_of_le (by positivity) hd
  have bd (t : ℝ) (ht : |t| ≤ T) : ‖char A j t‖ ≤ exp (-(radius t)^2/32) := by
    let α := (char A j t).arg
    let B := A.filter (fun p => |residue (t*offset j p-α)| ≤ radius t)
    let C := A \ B
    have hBC : B ⊆ A := filter_subset ..
    have hsplit : mass C + mass B = mass A := sum_sdiff hBC
    have rot := rotate_char A j t hmass
    have loss : mass A * (1-‖char A j t‖) =
        ∑ p ∈ A, (p:ℝ)⁻¹ * (1-cos (t*offset j p-α)) := by
      rw [mul_sub,mul_one,rot]; simp [mul_sub,sum_sub_distrib,mass,α]
    have hn (p : ℕ) : 0 ≤ (p:ℝ)⁻¹*(1-cos (t*offset j p-α)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one _))
    by_cases h0 : t = 0
    · have hh := sum_nonneg (s := A) (fun p _ => hn p)
      rw [← loss] at hh
      subst t
      simpa [radius] using (show ‖char A j 0‖ ≤ 1 by nlinarith)
    have hh := arc_small he (show e*(2*T+9) ≤ 1/100 by dsimp [e]; rw [div_mul_cancel₀ _ (by positivity)])
      hbox t α h0 ht (abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩)
    have hsub := filter_subset_filter (fun p => |residue (t*offset j p-α)| ≤ radius t) hA
    have hmB := mul_le_mul_of_nonneg_left (mono_mass hsub) hj'.le
    have hd' := (div_le_iff₀ (show 0 < 3*(j:ℝ) by positivity)).mp hd
    have hhalf : mass A / 2 ≤ mass C := by
      by_contra! hh'
      nlinarith [mul_pos hj' (show 0 < mass B - mass A/2 by linarith)]
    have hR : 0 ≤ radius t := by dsimp [radius]; positivity
    have hsum : mass C * (radius t^2/16) ≤ mass A * (1-‖char A j t‖) := by
      rw [loss,mass,sum_mul]
      refine le_trans (sum_le_sum ?_) (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ => hn p))
      intro p hp
      obtain ⟨ha,hb⟩ := mem_sdiff.mp hp
      have hlarge : radius t ≤ |residue (t*offset j p-α)| := by
        exact le_of_not_ge (fun hh => hb (mem_filter.mpr ⟨ha,hh⟩))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [cos_drop (t*offset j p-α), sq_abs (residue (t*offset j p-α)),
        pow_le_pow_left₀ hR hlarge 2]
    refine le_trans ?_ (Real.add_one_le_exp _)
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg (radius t)),
      mul_pos hmass (show 0 < ‖char A j t‖ - (-(radius t)^2/32+1) by linarith)]
  constructor
  · intro t ht
    have h := bd t (ht.trans hT)
    convert h using 2
    rw [radius,min_eq_right ht,div_pow,sq_abs]; ring
  · intro t ht hTm
    have h := bd t (hTm.trans (le_max_right ..))
    convert h using 2
    rw [radius,min_eq_left ht.le]; norm_num

#print axioms prime_cells_of_rectangles
end Shift490

import OldSparseMass
import TransplantColors
import LargeLabelTransfer

/-! Sparse recovery from the finite red word realization, including the
case of an empty good window. The old errors here have Euler normalization. -/
namespace Erdos490Transfer
open Filter Finset Real Shift490 Erdos490Smooth Erdos490PrimeCells
noncomputable section
open Classical

/-- Finite frozen-input form of the red sampling and word counts. The
premise concerns only nonempty families of actual good old integers. -/
def RedGoodRealization : Prop :=
  ∀ (C : Finset ℕ), (∀ p ∈ C, p.Prime) → ∀ c : ℝ,
    (∀ p ∈ C, ∀ v ∈ Set.Icc (boundary Mertens.M p) (boundary Mertens.M (p+1)),
      |v-log p| ≤ c/log p^2) →
    ∀ z B δ : ℝ, 0 < B → 0 < δ → 0 < z-B-δ →
    let G := goodWindow C (z-B) z δ (fun p => c/log p^2)
    G.Nonempty → ∃ x ∈ Set.Icc (z-B-δ) (z+δ), ∀ u : ℕ, 0 < u → ∀ η > 0,
      ∀ᶠ m : ℕ in atTop, exp (-2*δ)*exp (-z)*(G.card:ℝ) - η ≤
        (log m/x)*density (bands Mertens.M (log m/x) C) m u

private lemma red_absorb {F₀ G X a E θ : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E)
    (hcap : F₀ ≤ 2*K₀*E) (ho : F₀-2*a*E ≤ G) (hG : 0 ≤ G)
    (hr : exp (-2*a)*G-a*E ≤ X) (hsmall : (4*K₀+3)*a ≤ θ) :
    F₀ ≤ X+θ*E := by
  have hex : 1-2*a ≤ exp (-2*a) := by linarith [add_one_le_exp (-2*a)]
  by_cases h : F₀-2*a*E ≤ 0
  · have hX := mul_nonneg (exp_pos (-2*a)).le hG
    have h3 : 3*a ≤ θ := by nlinarith [mul_nonneg K₀_pos.le ha]
    nlinarith only [h,hr,hX,mul_le_mul_of_nonneg_right h3 hE]
  have low := mul_le_mul hex ho (le_of_not_ge h) (exp_pos _).le
  nlinarith only [low,hr,mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2*a by positivity),
    mul_le_mul_of_nonneg_right hsmall hE,mul_nonneg (sq_nonneg a) hE]

/-- Every sufficiently large auxiliary cutoff admits sparse recovery at
a common sample near any prescribed bounded-shift old peak. -/
theorem red_from_good (realize : RedGoodRealization) {ε : ℝ} (hε : 0 < ε) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ y : ℕ in atTop, ∀ᶠ z : ℝ in atTop,
    ∀ N : ℕ, 0 < log (N:ℝ) → log N ≤ 2*z →
    ∀ C ⊆ (Ioc y N).filter Nat.Prime,
      ∃ x : ℝ, 0 < x ∧ |x-z| ≤ B' ∧ ∀ u : ℕ, 0 < u → ∀ᶠ m : ℕ in atTop,
      F C z ≤ (log m/x)*density (bands Mertens.M (log m/x) C) m u + ε*(P C/log N) := by
  let a := ε/(4*K₀+3)
  have denom : 0 < 4*K₀+3 := by linarith [K₀_pos]
  have ha : 0 < a := div_pos hε denom
  have hcoef : (4*K₀+3)*a = ε := by dsimp [a]; field_simp
  obtain ⟨c,hc,hdisp⟩ := cell_displacement
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp hdisp
  obtain ⟨B,hB,hy⟩ := sparse_good_window hc.le ha ha
  refine ⟨B+a,by positivity,?_⟩
  filter_upwards [hy,eventually_ge_atTop p₀] with y hy hy0
  filter_upwards [hy,eventually_gt_atTop (B+a)] with z hz hz0
  intro N hN hL C hC
  have nz : 0 < z := by linarith
  have hNp : 0 < (N:ℝ) := by
    by_contra! h
    have : N=0 := by exact_mod_cast (le_antisymm h (Nat.cast_nonneg _))
    simp [this] at hN
  have hnexp := (log_le_iff_le_exp hNp).mp hL
  have hl := hz N (by simpa [mul_comm] using hnexp) C hC
  let E := P C/log N
  let G := goodWindow C (z-B) z a (fun p => c/log p^2)
  have hE : 0 < E := div_pos (P_pos _) hN
  have ratio : P C/z ≤ 2*E := by
    dsimp [E]
    rw [← mul_div_assoc,div_le_div_iff₀ nz hN]
    nlinarith only [mul_le_mul_of_nonneg_left hL (P_pos C).le]
  have old : F C z-2*a*E ≤ exp (-z)*G.card := by
    change F C z-a*(P C/z) ≤ exp (-z)*G.card at hl
    linarith only [hl,mul_le_mul_of_nonneg_left ratio ha.le]
  have cap : F C z ≤ 2*K₀*E := (counting_bound C z nz).trans (by
    rw [mul_div_assoc]; nlinarith only [mul_le_mul_of_nonneg_left ratio K₀_pos.le])
  have pr : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  by_cases nonempty : G.Nonempty
  · obtain ⟨x,hx,hr⟩ := realize C pr c (fun p h => hp₀ p (hy0.trans
      (mem_Ioc.mp (mem_filter.mp (hC h)).1).1.le) (pr _ h)) z B a hB ha (by linarith) nonempty
    refine ⟨x,by linarith [hx.1],abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
    intro u hu
    filter_upwards [hr u hu (a*E) (mul_pos ha hE)] with m hm
    apply red_absorb ha.le hE.le cap old (by positivity) _ hcoef.le
    simpa only [mul_assoc] using hm
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [hempty,card_empty,Nat.cast_zero,mul_zero] at old
    refine ⟨z,nz,by simp; positivity,?_⟩
    intro u hu
    apply Eventually.of_forall
    intro m
    have nonneg : 0 ≤ (log (m:ℝ)/z)*density (bands Mertens.M (log m/z) C) m u :=
      mul_nonneg (div_nonneg (log_natCast_nonneg _) nz.le) (by unfold density; positivity)
    have h2 : 2*a ≤ ε := by nlinarith [mul_nonneg K₀_pos.le ha.le]
    linarith only [old,nonneg,mul_le_mul_of_nonneg_right h2 hE.le]

#print axioms red_from_good
end
end Erdos490Transfer

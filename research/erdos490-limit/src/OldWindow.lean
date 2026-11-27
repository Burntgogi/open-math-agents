import OldStrip
import SmoothMass

/-! Exact Stieltjes partial summation for old harmonic windows and a
uniform estimate when the stripped color density is flat on the window. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 MeasureTheory
open scoped Interval Topology
noncomputable section
open Classical

def oldWindow (C : Finset ℕ) (a b : ℝ) : Finset ℕ :=
  (semigroup C ⌊exp b⌋₊).filter (fun m : ℕ => a < log m)

def windowMass (C : Finset ℕ) (a b : ℝ) :=
  ∑ m ∈ oldWindow C a b, (m:ℝ)⁻¹

lemma mem_oldWindow {m : ℕ} {C : Finset ℕ} {a b : ℝ} : m ∈ oldWindow C a b ↔
    Active C m ∧ a < log m ∧ log m ≤ b := by
  rw [oldWindow,mem_filter,mem_semigroup]
  constructor
  · rintro ⟨⟨hm,hl⟩,ha⟩
    exact ⟨hm,ha,(log_le_iff_le_exp (nat_pos ⟨m,hm⟩)).mpr ((Nat.le_floor_iff (exp_pos b).le).mp hl)⟩
  · rintro ⟨hm,ha,hb⟩
    exact ⟨⟨hm,Nat.le_floor ((log_le_iff_le_exp (nat_pos ⟨m,hm⟩)).mp hb)⟩,ha⟩

private def after (C : Finset ℕ) (a : ℝ) (n : Integers C) : ℝ :=
  if a < logN n then ((n:ℕ):ℝ)⁻¹ else 0

private lemma after_sum (C a) : Summable (after C a) := by
  apply Summable.of_nonneg_of_le _ _ (harmonic_sum C).summable
  · intro n; unfold after; split <;> positivity
  · intro n; unfold after; split <;> simp

private lemma tail_decompose (C a) :
    (∫ t in Set.Ioi a, F C t) = F C a + ∑' n : Integers C, after C a n := by
  rw [Erdos490Smooth.kernel_tail_integral,F,← (summable_atom C a).tsum_add (after_sum C a)]
  apply tsum_congr
  intro n
  by_cases hn : logN n ≤ a
  · simp [atom,after,hn,not_lt.mpr hn]
  · simp [max_eq_right (le_of_not_ge hn),atom,after,hn,lt_of_not_ge hn,exp_neg,logN,exp_log (nat_pos n)]

private lemma after_split (C : Finset ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∑' n, after C a n) = windowMass C a b + ∑' n, after C b n := by
  let f (n : Integers C) : ℝ := if a < logN n ∧ logN n ≤ b then ((n:ℕ):ℝ)⁻¹ else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le _ _ (harmonic_sum C).summable
    · intro n; dsimp [f]; split <;> positivity
    · intro n; dsimp [f]; split <;> simp
  have hwin : windowMass C a b = ∑' n, f n := by
    let s := (oldWindow C a b).subtype (· ∈ Integers C)
    have hm (n : Integers C) : n ∈ s ↔ a < logN n ∧ logN n ≤ b := by
      simp [s,mem_oldWindow,n.property,logN]
    rw [tsum_eq_sum (s:=s) (fun n hn => by simp [f,mt (hm n).mpr hn])]
    calc
      _ = ∑ n ∈ s, ((n.val:ℕ):ℝ)⁻¹ := by
        have eq : s.image Subtype.val = oldWindow C a b := by
          ext m
          constructor
          · rintro hx
            obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
            exact mem_oldWindow.mpr ⟨v.property,(hm v).mp hv⟩
          · intro hx
            obtain ⟨hact,ha,hb⟩ := mem_oldWindow.mp hx
            exact mem_image.mpr ⟨⟨m,hact⟩,(hm _).mpr ⟨ha,hb⟩,rfl⟩
        rw [windowMass,← eq,sum_image (fun _ _ _ _ he => Subtype.ext he)]
      _ = _ := sum_congr rfl (fun n hn => (if_pos ((hm n).mp hn)).symm)
  rw [hwin,← hf.tsum_add (after_sum C b)]
  apply tsum_congr
  intro n
  dsimp [after,f]
  by_cases h1 : a < logN n <;> by_cases h2 : b < logN n <;> simp_all [not_lt]
  linarith

/-- Exact on (a,b], including both endpoint atoms with their correct sign. -/
theorem window_identity (C : Finset ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    windowMass C a b = F C b-F C a + ∫ t in a..b, F C t := by
  have h0 : IntegrableOn (F C) (Set.Ioi 0) := by
    by_contra hn
    have eq := integral_undef hn
    rw [Erdos490Smooth.kernel_mass] at eq
    exact (P_pos C).ne' eq
  have ht := intervalIntegral.integral_Ioi_sub_Ioi (h0.mono_set (Set.Ioi_subset_Ioi ha)) hab
  rw [tail_decompose,tail_decompose,after_split C hab] at ht
  linarith

/-- Uniform in both moving endpoints. A sup error e in the density costs
(2+b-a)e in the old harmonic mass. -/
theorem window_flat (C : Finset ℕ) {a b r e : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ t ∈ Set.Icc a b, |F C t-r| ≤ e) :
    |windowMass C a b-(b-a)*r| ≤ (2+b-a)*e := by
  have h0 : IntegrableOn (F C) (Set.Ioi 0) := by
    by_contra hn
    have eq := integral_undef hn
    rw [Erdos490Smooth.kernel_mass] at eq
    exact (P_pos C).ne' eq
  have hint : IntervalIntegrable (F C) volume a b :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le hab |>.mpr
      (h0.mono_set (fun x hx => ha.trans_lt hx.1))
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => F C t-r) (a:=a) (b:=b) (C:=e) (fun t ht =>
      by rw [Set.uIoc_of_le hab] at ht; exact h t ⟨ht.1.le,ht.2⟩)
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hab)] at he
  have hl := abs_le.mp (h a ⟨le_rfl,hab⟩)
  have hr := abs_le.mp (h b ⟨hab,le_rfl⟩)
  rw [window_identity C ha hab,abs_le]
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2]

/-- Old harmonic mass on every moving interval in a fixed window after
removing an arbitrary subset of a fixed finite prime pool. -/
theorem stripped_window_mass {Y N c b} (hN : StrictMono N) (st : Stable (Y:=Y) N c b)
    (pool : Finset ℕ) (hp : ∀ p ∈ pool, p.Prime) {H η : ℝ} (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ S ⊆ pool, S ⊆ pick (c k) b → ∀ a d : ℝ, a ≤ d →
      log (N k)-H ≤ a → d ≤ log (N k)+H →
      let C := pick (c k) b
      |windowMass (C \ S) a d - (d-a)*((P S)⁻¹*F C (log (N k)))| ≤
        (2+d-a)*(η*(P (C \ S)/log (N k))) := by
  have large := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop)).eventually_ge_atTop H
  filter_upwards [large,stable_strip st pool hp H η hH hη] with k hk hstrip
  change H ≤ log (N k) at hk
  intro S hS hC a d had ha hd
  apply window_flat _ (by linarith : 0 ≤ a) had
  intro t ht
  have h := hstrip S hS hC (t-log (N k)) (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  rwa [show log (N k)+(t-log (N k))=t by ring] at h

#print axioms stripped_window_mass
#print axioms window_identity
#print axioms window_flat
end
end Erdos490Transfer

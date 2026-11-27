import RedGood
import BlueStable

/-! Exact site H2 from the finite good sparse-word estimate. The auxiliary
threshold, old prime stripping, good-product losses, blue realization,
normalization and completion of the common coloring are internal. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells
noncomputable section
open Classical

private lemma coarse_subset {Y n y} (co : Colors Y n) (b : Bool) :
    roughColor (primes Y y) (pick co b) ⊆ (Ioc y n).filter Nat.Prime := by
  intro p h
  obtain ⟨hC,hlo⟩ := mem_sdiff.mp h
  have hu : p ∈ co.red ∪ co.blue := by cases b <;> simp_all [pick]
  rw [co.cover] at hu
  obtain ⟨hp,pr⟩ := mem_filter.mp hu
  have hpy : y < p := by
    by_contra! hn
    exact hlo (mem_inter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hp).1,hn⟩,pr⟩,hC⟩)
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpy,(mem_Icc.mp hp).2⟩,pr⟩

private def swap {Y n} (c : Colors Y n) : Colors Y n :=
  ⟨c.blue,c.red,(union_comm ..).trans c.cover,c.separate.symm⟩

private theorem oriented_target {Y y : ℕ} {x : ℝ} (hx : 0 < x) (b : Bool) {Q R : Finset ℕ}
    (hd : Disjoint Q R) (hq : ∀ p ∈ Q, y < p) (hr : ∀ p ∈ R, y < p) :
    ∃ d : ∀ n, Colors Y n, ∀ᶠ n : ℕ in atTop, ∀ u : ℕ,
      let t := log n/x
      density (bands Mertens.M t Q) n u ≤ density (pick (d n) (!b)) n u ∧
      density (bands Mertens.M t R ∪ smoothLabels (Y-1) (exp (t*width y))) n u ≤
        density (pick (d n) b) n u := by
  let pred (n : ℕ) (c : Colors Y n) := ∀ u : ℕ, let t := log n/x
    density (bands Mertens.M t Q) n u ≤ density (pick c (!b)) n u ∧
    density (bands Mertens.M t R ∪ smoothLabels (Y-1) (exp (t*width y))) n u ≤ density (pick c b) n u
  let blank (n : ℕ) : Colors Y n := ⟨∅,primes Y n,empty_union _,disjoint_empty_left _⟩
  let d (n : ℕ) := if h : ∃ c, pred n c then h.choose else blank n
  refine ⟨d,?_⟩
  have lim := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  filter_upwards [lim.eventually (eventually_transplant_cutoff Y y Mertens.M),
    lim.eventually_ge_atTop 0] with n hY ht
  obtain ⟨_,c,hc⟩ := transplant_colors (n:=n) hd hq hr Mertens.M ht hY
  have den {A B : Finset ℕ} {u : ℕ} (h : semigroup A (n/u) ⊆ semigroup B (n/u)) :
      density A n u ≤ density B n u := by
    unfold density
    gcongr
  have he : ∃ c, pred n c := by
    cases b
    · exact ⟨c,fun u => by simpa [pick,width] using And.intro (den (hc u).1) (den (hc u).2)⟩
    · exact ⟨swap c,fun u => by simpa [pick,swap,width] using And.intro (den (hc u).1) (den (hc u).2)⟩
  change pred n (d n)
  simpa only [d,dif_pos he] using he.choose_spec

theorem large_labels_of_red_good (red : RedGoodRealization) : LargeLabelRecovery := by
  intro Y K ε hε hε1
  obtain ⟨B,hB,hy⟩ := red_from_good red hε
  obtain ⟨y,⟨hs,hb⟩,hyY⟩ := ((hy.and (blue_stable_recovery Y hε)).and (eventually_ge_atTop Y)).exists
  refine ⟨y,hyY,?_⟩
  intro N mono co b
  dsimp only
  let Q (k : ℕ) := roughColor (primes Y y) (pick (co k) (!b))
  let R (k : ℕ) := roughColor (primes Y y) (pick (co k) b)
  intro flat z hz
  obtain ⟨W,hW⟩ := hz
  let H := |W|+B
  have hH : 0 ≤ H := add_nonneg (abs_nonneg _) hB
  have cq (k : ℕ) := coarse_subset (y:=y) (co k) (!b)
  have cr (k : ℕ) := coarse_subset (y:=y) (co k) b
  have blue := hb N mono R cr flat H hH
  let L (k : ℕ) := log (N k:ℝ)
  have lim : Tendsto L atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp mono.tendsto_atTop)
  have zlim : Tendsto z atTop atTop := tendsto_atTop.mpr (fun r => by
    filter_upwards [hW,lim.eventually_ge_atTop (r+W)] with k h hk
    change |z k-L k| ≤ W at h
    linarith [(abs_le.mp h).1])
  apply Eventually.frequently
  filter_upwards [blue,zlim.eventually hs,hW,lim.eventually_gt_atTop (2*|W|+2),
    lim.eventually_ge_atTop (H/ε),mono.tendsto_atTop.eventually_ge_atTop 2] with k hk hred hw hL hsize hn
  change |z k-L k| ≤ W at hw
  have hL0 : 0 < L k := by linarith [abs_nonneg W]
  obtain ⟨x,hx,hxz,hqr⟩ := hred (N k) hL0 (by
    change L k ≤ 2*z k; linarith [(abs_le.mp hw).1,le_abs_self W]) (Q k) (cq k)
  have near : |x-L k| ≤ H := (abs_sub_le x (z k) (L k)).trans (by
    dsimp [H]; linarith [le_abs_self W])
  have close : (1-ε)*L k ≤ x := by
    have h := (div_le_iff₀ hε).mp hsize
    linarith [(abs_le.mp near).1]
  have sep : Disjoint (Q k) (R k) := by
    apply Disjoint.mono sdiff_subset sdiff_subset
    cases b <;> simp [pick,(co k).separate,(co k).separate.symm]
  obtain ⟨d,hd⟩ := oriented_target (Y:=Y) hx b sep
    (fun p h => (mem_Ioc.mp (mem_filter.mp (cq _ h)).1).1)
    (fun p h => (mem_Ioc.mp (mem_filter.mp (cr _ h)).1).1)
  refine ⟨hn,x,hx,close,d,?_,?_⟩
  · intro i _
    filter_upwards [hd,hqr (i+1) (by omega)] with m hm hr
    exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left (hm (i+1)).1
      (div_nonneg (log_natCast_nonneg m) hx.le)) le_rfl)
  · intro i _
    filter_upwards [hd,hk x near (i+1) (by omega)] with m hm hr
    exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left (hm (i+1)).2 (inv_pos.mpr (P_pos (primes Y y))).le) le_rfl)

theorem site_H2_of_red_good (red : RedGoodRealization) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_large_labels (large_labels_of_red_good red)

#print axioms site_H2_of_red_good
end
end Erdos490Transfer

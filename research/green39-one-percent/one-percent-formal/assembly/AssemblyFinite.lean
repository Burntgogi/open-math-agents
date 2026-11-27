import AssemblyModel
import PrivateBalance
import FourierSparsification
import TerminalConcentration

/-! Canonical covers, balanced splits, retained terminals and fitted witnesses. -/

open Finset Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split OnePercent.Fourier

abbrev space (p : ℕ) [NeZero p] :=
  orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt)

def terminalOK (C : Catalog p) (A : Points p) : Prop :=
  ∀ P ∈ C.containers C.stages, Terminal.CoversOutside P p.sqrt 0.02 A

def smoothBad (C : Catalog p) (q : Sample p) : Prop :=
  ∃ i < C.stages, ∃ μ ∈ C.laws i, ¬ typical μ q

def hitBad (C : Catalog p) (q : Sample p) : Prop :=
  ∃ i < C.stages, ∃ w ∈ witnesses C i, hits w q

def cover (p : ℕ) [NeZero p] (A : Points p) :=
  ∃ T : Points p, T.card ≤ ⌊1.01*(p.sqrt : ℝ)⌋₊ ∧ A + T = univ

theorem card_union_sample {q : Sample p} (hq : q ∈ space p) :
    (q.1 ∪ q.2).card = p.sqrt := by
  have h := (mem_powersetCard.mp (orderedPairs_union_mem hq)).2
  dsimp [half,rest] at h
  omega

/-- The upstream floor budget implies eligibility for the canonical cover. -/
theorem small_of_cover {A : Points p} (ha : A.card = p.sqrt) (hk : 0 < p.sqrt)
    (hc : cover p A) : (smallCovers A).Nonempty := by
  obtain ⟨T,ht,hcover⟩ := hc
  refine ⟨T, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),hcover,?_⟩⟩
  have h₁ : (T.card : ℝ) ≤ 1.01*p.sqrt :=
    (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))
  have h₂ : (p.sqrt : ℝ)^2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  rw [ha,le_div_iff₀ (Nat.cast_pos.mpr hk)]
  nlinarith [mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg p.sqrt)]

/-- Starting from a true upstream cover yields a concrete failed event on every split. -/
theorem witness_inclusion {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt)
    (hsparse : ∀ i < C.stages, 8*Real.log (4*(p:ℝ)) <
      (sMax p.sqrt : ℝ) * eta (x p i)^2)
    {q : Sample p} (hq : q ∈ space p) (hc : cover p (q.1 ∪ q.2)) :
    CanonicalBalanceFailure q ∨ ¬ terminalOK C (q.1 ∪ q.2) ∨ smoothBad C q ∨ hitBad C q := by
  classical
  let k := p.sqrt
  let A := q.1 ∪ q.2
  let T := canonicalCover A
  let G := nearPrivateCenters A T (0.0225*A.card)
  have ha : A.card = k := card_union_sample hq
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 100000) hk
  have hk0' : (0:ℝ) < k := Nat.cast_pos.mpr hk0
  have hsmall := small_of_cover ha hk0 hc
  have hT := (mem_filter.mp (canonicalCover_spec hsmall).1).2
  change A + T = univ ∧ (T.card : ℝ) ≤ 1.01*p/A.card at hT
  have hg := card_nearPrivateCenters_onePercent hT.1 (ha ▸ hk0)
    (ha ▸ Nat.sqrt_le' p) hT.2
  have hstart : (k : ℝ)/9 ≤ G.card := ha ▸ hg.2.2.trans (hg.2.1.trans hg.1)
  have hGT : G ⊆ T := fun _ ht => (mem_nearPrivateCenters.mp ht).1
  have hm := numerical (p := p) hk (Nat.lt_succ_sqrt' p)
  have hTk : (T.card : ℝ) * k ≤ 1.01*p := (le_div_iff₀ hk0').mp (ha ▸ hT.2)
  have hTk' : (T.card : ℝ) ≤ 2*k := by
    apply (le_of_mul_le_mul_right _ hk0')
    nlinarith only [hm.1,hTk,sq_nonneg (k:ℝ)]
  have hGk := (Nat.cast_le.mpr (card_le_card hGT)).trans hTk'
  by_cases hb : BalanceFailure A T q.1 q.2
  · exact Or.inl ⟨hsmall,hb⟩
  right
  by_cases hnt : ¬ terminalOK C A
  · exact Or.inl hnt
  right
  have ht := Classical.not_not.mp hnt
  by_cases hs : smoothBad C q
  · exact Or.inl hs
  right
  rcases iterate spec G hk0 hstart hGk with
    ⟨i,hi,P,hP,V,hVP,hVG,hV,F,hFV,hF,μ,hμ,hfit⟩ | ⟨P,hP,hret⟩
  · have hFp : F.Nonempty := by
      apply card_pos.mp
      have hx : 0 < x p i := lt_trans (by norm_num) (spec.active i hi)
      have hpos : 0 < (p.sqrt:ℝ)*Transcripts.lossRate (x p i) := by unfold Transcripts.lossRate; positivity
      exact_mod_cast hpos.trans_le hF
    obtain ⟨S,hSF,hsz,hfitS⟩ := exists_fourierFit_sparsify F μ (sMax k) (Real.exp_nonneg _)
      hfit (fun _ _ => hsparse i hi)
    have hSp : S.Nonempty := card_pos.mp (hsz ▸ lt_min hFp.card_pos (by dsimp [sMax,k]; omega))
    have hrV : rSize k ≤ V.card := by
      have hr : 10*rSize k ≤ k := by simpa [Nat.mul_comm] using Nat.div_mul_le_self k 10
      have hr' : 10*(rSize k:ℝ) ≤ k := by exact_mod_cast hr
      change (0.11:ℝ)*k ≤ V.card at hV
      exact_mod_cast (show (rSize k:ℝ) ≤ V.card by linarith)
    obtain ⟨R,hR₀⟩ := powersetCard_nonempty.mpr hrV
    obtain ⟨hRV,hr⟩ := mem_powersetCard.mp hR₀
    have hRp : R.Nonempty := card_pos.mp (hr ▸ (by dsimp [rSize,k]; omega))
    have hRG := hRV.trans hVG
    have hSG := (hSF.trans hFV).trans hVG
    have hbal (t) (h : t ∈ G) :
        ((nonprivateLabels A T q.1 t).card : ℝ) ≤ 0.0114*A.card ∧
        ((nonprivateLabels A T q.2 t).card : ℝ) ≤ 0.0114*A.card :=
      ⟨le_of_not_gt fun hh => hb ⟨t,h,Or.inl hh⟩,le_of_not_gt fun hh => hb ⟨t,h,Or.inr hh⟩⟩
    obtain ⟨_,h1,_,h2,hd⟩ := mem_orderedPairs.mp hq
    have hpriv := balanced_halves_bounds (show q.1 ∪ q.2 = A from rfl) hd (by rw [ha]; exact h1)
      (hRG.trans hGT) (hSG.trans hGT) (fun t ht => (hbal t (hRG ht)).1)
      (fun t ht => (hbal t (hSG ht)).2)
    obtain ⟨hl,hu⟩ := hpriv
    rw [ha] at hl hu
    have htyp : typical μ q := by_contra fun hn => hs ⟨i,hi,μ,hμ,hn⟩
    let U := q.1 + R
    have hpred := sum_predicted_ge_of_l1 q.2 U S μ htyp.1
    have hbase : (0.244 : ℝ)*R.card ≤ (q.2.card:ℝ)*U.card/p - 0.00000001*k := by
      rw [h2]
      have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (rest k))) (Nat.cast_nonneg p)
      rw [hr] at h ⊢
      rw [←mul_assoc] at h
      exact hm.2.2.trans (sub_le_sub_right h _)
    have hpred' : (0.244:ℝ)*R.card*S.card ≤ ∑ z ∈ q.2, predicted U S μ z := by
      linarith only [hpred,mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg S.card)]
    have hobs : (∑ z ∈ q.2, observed U S z) ≤ (0.115:ℝ)*R.card*S.card := by
      have hcoef : (0.0114:ℝ)*k ≤ 0.115*R.card := by rw [hr]; linarith only [hm.2.1]
      simp only [Nat.cast_sum, singleton_add] at hu
      exact hu.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg S.card))
    have hh := (exceptionalHits_section5 q.1 q.2 R S μ hk0 hRp hSp
      (by rw [h2]; exact Nat.sub_le _ _) (spec.capped i hi μ hμ).1 hpred' hobs
      (fun v _ => htyp.2 v)).2
    refine ⟨i,hi,(R,S,μ),mem_biUnion.mpr ⟨P,hP,mem_filter.mpr ⟨?_,hfitS⟩⟩,hh.le⟩
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨hRV.trans hVP,hr⟩,mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_powerset.mpr ((hSF.trans hFV).trans hVP),hSp,hsz ▸ min_le_right ..⟩,hμ⟩⟩
  · have hout := ht P hP T hT.1
    have hinter : ((G ∩ P).card:ℝ) ≤ (T ∩ P).card :=
      Nat.cast_le.mpr (card_le_card (inter_subset_inter_right hGT))
    have he : ((T \ P).card:ℝ) + (T ∩ P).card = T.card := by exact_mod_cast card_sdiff_add_card_inter T P
    have hl := (div_le_iff₀ hk0').mp hout
    change (0.11:ℝ)*k ≤ _ at hret
    have hn : (0.11:ℝ)*k ≤ (T.card:ℝ) - (T \ P).card := by linarith
    exfalso
    nlinarith only [mul_le_mul_of_nonneg_right hn hk0'.le,hl,hTk,hm.1,sq_pos_of_pos hk0']

end
end Green39.Assembly
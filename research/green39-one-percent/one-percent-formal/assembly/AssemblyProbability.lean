import AssemblyFinite
import AssemblyBounds

/-! Pushforward and finite union estimates for the cover event. -/

open Finset Real Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split Concentration

theorem prob_or {α} (S : Finset α) (E F : α → Prop) :
    probability S (fun a => E a ∨ F a) ≤ probability S E + probability S F := by
  classical
  unfold probability
  rw [← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply (card_le_card ?_).trans (card_union_le _ _)
  intro a ha
  simp only [mem_filter] at ha
  obtain ⟨h,h₁|h₂⟩ := ha
  · exact mem_union_left _ (mem_filter.mpr ⟨h,h₁⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨h,h₂⟩)

/-- Exact pushforward of the disjoint-pair law to the uniform union slice. -/
theorem union_law (E : Points p → Prop) :
    probability (space p) (fun q => E (q.1 ∪ q.2)) =
      sliceProbability (univ : Points p) p.sqrt E := by
  classical
  rw [probability_eq_mean_union]
  have hsum : half p.sqrt + rest p.sqrt = p.sqrt := by dsimp [half,rest]; omega
  rw [hsum]
  let D := (univ : Points p).powersetCard p.sqrt
  have hfib (A : Points p) (hA : A ∈ D) :
      sliceProbability A (half p.sqrt) (fun B => E (B ∪ (A \ B))) = if E A then 1 else 0 := by
    have ha := (mem_powersetCard.mp hA).2
    have hn : (A.powersetCard (half p.sqrt)).Nonempty :=
      powersetCard_nonempty.mpr (ha ▸ Nat.div_le_self _ _)
    have hfilter : (A.powersetCard (half p.sqrt)).filter (fun B => E (B ∪ (A \ B))) =
        (A.powersetCard (half p.sqrt)).filter (fun _ => E A) := by
      ext B
      simp only [mem_filter]
      apply and_congr_right
      intro hB
      have hu : B ∪ (A \ B) = A := sup_sdiff_cancel_right (mem_powersetCard.mp hB).1
      rw [hu]
    unfold sliceProbability
    rw [hfilter]
    split_ifs with he
    · simp [he, Nat.choose_pos (show half p.sqrt ≤ A.card by rw [ha]; exact Nat.div_le_self _ _)|>.ne']
    · simp [he]
  unfold mean
  change (∑ A ∈ D, sliceProbability A (half p.sqrt) (fun B => E (B ∪ (A \ B)))) / D.card = ((D.filter E).card:ℝ)/D.card
  rw [sum_congr rfl hfib, ← sum_filter]
  simp [D]

theorem hit_union {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt) :
    probability (space p) (hitBad C) ≤
      (∑ i ∈ range C.stages, ((C.containers i).card:ℝ) * (C.laws i).card) *
        exp (-468*(p.sqrt:ℝ)) := by
  classical
  have h0 := probability_exists_le_sum (space p) (range C.stages)
    (fun i q => ∃ w ∈ witnesses C i, hits w q)
  simp only [mem_range] at h0
  apply h0.trans
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hi' := mem_range.mp hi
  have h1 := probability_exists_le_sum (space p) (witnesses C i) hits
  apply h1.trans
  calc
    _ ≤ ∑ _ ∈ witnesses C i, hitBound p.sqrt (x p i) :=
      sum_le_sum fun w hw => witness_probability spec hi' hk hw
    _ = _ := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (count_witnesses spec hi') (by unfold hitBound hitBase; positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left (paid_witnesses _ ((by norm_num : (0:ℝ) ≤ 5000).trans (spec.active _ hi').le)) (by positivity)

def allLaws (C : Catalog p) := (range C.stages).biUnion C.laws

theorem smooth_union (C : Catalog p) (b : ℝ)
    (hb : ∀ μ ∈ allLaws C, probability (space p) (fun q => ¬ typical μ q) ≤ b) :
    probability (space p) (smoothBad C) ≤ ((allLaws C).card:ℝ)*b := by
  have hu := probability_exists_le_sum (space p) (allLaws C) (fun μ q => ¬typical μ q)
  calc
    _ ≤ probability (space p) (fun q => ∃ μ ∈ allLaws C, ¬typical μ q) := by
      apply probability_mono
      rintro q _ ⟨i,hi,μ,hμ,h⟩
      exact ⟨μ,mem_biUnion.mpr ⟨i,mem_range.mpr hi,hμ⟩,h⟩
    _ ≤ _ := hu.trans (by rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hb)

theorem cover_upper {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt)
    (hsparse : ∀ i < C.stages, 8*log (4*(p:ℝ)) < (sMax p.sqrt:ℝ)*eta (x p i)^2)
    (b : ℝ) (hb : ∀ μ ∈ allLaws C, probability (space p) (fun q => ¬typical μ q) ≤ b) :
    sliceProbability (univ : Points p) p.sqrt (cover p) ≤
      2*p*exp (-(p.sqrt:ℝ)/200000000) +
      sliceProbability (univ : Points p) p.sqrt (fun A => ¬terminalOK C A) +
      ((allLaws C).card:ℝ)*b +
      (∑ i ∈ range C.stages, ((C.containers i).card:ℝ)*(C.laws i).card)*exp (-468*(p.sqrt:ℝ)) := by
  rw [← union_law, ← union_law (fun A => ¬terminalOK C A)]
  have hm := probability_mono (fun q hq hc => witness_inclusion spec hk hsparse hq hc)
  have ho := prob_or (space p) CanonicalBalanceFailure (fun q => ¬terminalOK C (q.1 ∪ q.2) ∨ smoothBad C q ∨ hitBad C q)
  have ht := prob_or (space p) (fun q => ¬terminalOK C (q.1 ∪ q.2)) (fun q => smoothBad C q ∨ hitBad C q)
  have hs := prob_or (space p) (smoothBad C) (hitBad C)
  have hbal := canonical_balance_failure_bound (p:=p) (k:=p.sqrt) (by omega)
  linarith only [hm,ho,ht,hs,hbal,smooth_union C b hb,hit_union spec hk]

end
end Green39.Assembly
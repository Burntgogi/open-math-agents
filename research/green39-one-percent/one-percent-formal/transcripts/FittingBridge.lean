import FittingReplay
import FitStage

/-! An adapter for the fitting implementation's newest-first transcripts. -/

namespace Green39.Transcripts

open Finset

noncomputable section

variable {P σ : Type*} [Fintype P] [DecidableEq P] [Fintype σ]

def instructionEquiv {p : ℕ} (hσ : Fintype.card σ = 2 * p) :
    Fitting.Instruction σ ≃ Instruction p :=
  Fintype.equivOfCardEq (by
    rw [card_instruction]
    simp only [Fitting.Instruction, Fintype.card_option, Fintype.card_prod, Fintype.card_bool, hσ]
    omega)

/-- The fitting implementation stores the newest instruction first. -/
def encodeFittingWord {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (word : List (Fitting.Instruction σ)) : List (Instruction p) :=
  word.reverse.map (instructionEquiv hσ)

theorem encodeFittingWord_length {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (word : List (Fitting.Instruction σ)) :
    (encodeFittingWord hσ word).length = word.length := by
  simp [encodeFittingWord]

def fittingStage {p : ℕ} (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) (η cap : ℝ) :
    Stage (P → ℝ) (Instruction p) (P → ℝ) P where
  reset := uniformState
  step := fun m instruction =>
    Fitting.tilt m (Fitting.testAt tests cap m ((instructionEquiv hσ).symm instruction)) (η / 4)
  law := fun m => Fitting.clipped (Fitting.heavy cap m) m
  heavy := Fitting.heavy cap

theorem fittingStage_replay_eq {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (word : List (Fitting.Instruction σ)) :
    (fittingStage hσ tests η cap).replay (encodeFittingWord hσ word) =
      Fitting.decode tests η cap word := by
  induction word with
  | nil => rfl
  | cons instruction word ih =>
    simp only [encodeFittingWord, List.reverse_cons, List.map_append, Stage.replay, List.foldl_append,
      List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    change (fittingStage hσ tests η cap).step
      ((fittingStage hσ tests η cap).replay (encodeFittingWord hσ word))
        (instructionEquiv hσ instruction) = _
    rw [ih]
    simp [fittingStage, Fitting.decode]

theorem fittingStage_outputContainer_eq {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (records : List (List (Fitting.Instruction σ))) :
    (fittingStage hσ tests η cap).outputContainer (records.map (encodeFittingWord hσ)) =
      Fitting.recordedUnion tests η cap records := by
  induction records with
  | nil => rfl
  | cons word records ih =>
    simp only [List.map_cons, Stage.outputContainer, Stage.outputHeavy, fittingStage_replay_eq,
      Fitting.recordedUnion, ih]
    rfl

theorem recordedUnion_mem {p L R : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ)
    (records : List (List (Fitting.Instruction σ))) (hR : records.length ≤ R)
    (hL : ∀ word ∈ records, word.length ≤ L) :
    Fitting.recordedUnion tests η cap records ∈
      (fittingStage hσ tests η cap).containerList univ L R := by
  rw [← fittingStage_outputContainer_eq hσ tests η cap records]
  apply Stage.outputContainer_mem
  · simpa using hR
  · intro word hw
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hw
    exact ⟨(encodeFittingWord_length hσ source).trans_le (hL source hsource),
      fun _ _ => mem_univ _⟩

theorem fittedLaw_mem {p L : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (F : Finset P)
    (word : List (Fitting.Instruction σ)) (hL : word.length ≤ L)
    (hfit : Fitting.Fitted F tests η cap
      (Fitting.clipped (Fitting.heavy cap (Fitting.decode tests η cap word))
        (Fitting.decode tests η cap word))) :
    Fitting.clipped (Fitting.heavy cap (Fitting.decode tests η cap word))
        (Fitting.decode tests η cap word) ∈
      (fittingStage hσ tests η cap).cappedLawList (2 * cap) L := by
  refine (Stage.mem_cappedLawList _).mpr ⟨⟨⟨fun a => (hfit.2.1 a).1, hfit.1⟩,
    fun a => (hfit.2.1 a).2⟩, encodeFittingWord hσ word, ?_, ?_⟩
  · simpa only [encodeFittingWord_length] using hL
  · rw [Stage.outputLaw, fittingStage_replay_eq]
    rfl

theorem fittingStage_heavy_le {p H : ℕ} [Nonempty P] (hH : 0 < H)
    (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) (η : ℝ)
    (word : List (Instruction p)) :
    ((fittingStage hσ tests η (H : ℝ)⁻¹).outputHeavy word).card ≤ H := by
  let decodedWord := (word.map (instructionEquiv hσ).symm).reverse
  have hword : encodeFittingWord hσ decodedWord = word := by
    simp [encodeFittingWord, decodedWord, List.map_map, Function.comp_def]
  rw [← hword, Stage.outputHeavy, fittingStage_replay_eq]
  let m := Fitting.decode tests η (H : ℝ)⁻¹ decodedWord
  change (Fitting.heavy (H : ℝ)⁻¹ m).card ≤ H
  have hheavy : Fitting.heavy (H : ℝ)⁻¹ m = heavyAt (H : ℝ)⁻¹ m := by
    ext a
    simp [Fitting.heavy, mem_heavyAt]
  rw [hheavy]
  obtain ⟨hpos, hsum⟩ := Fitting.decode_law tests η (H : ℝ)⁻¹ decodedWord
  exact heavyAt_card_le hH ⟨fun a => (hpos a).le, hsum⟩

/-- The implementation's two alternatives land in the target-independent
families counted by the transcript bounds. -/
theorem fitting_stage_enumerated {p : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) {tests : σ → P → ℝ} (htests : ∀ j a, |tests j a| ≤ 1)
    {η cap θ : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (hcap : 0 ≤ cap) (hθ : 0 < θ)
    (L : ℕ) (hL : 16 * Real.log (Fintype.card P) < L * η ^ 2)
    (R : ℕ) (V : Finset P) (hR : (1 - η / 2) ^ R * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ μ ∈ (fittingStage hσ tests η cap).cappedLawList (2 * cap) L,
      Fitting.Fitted F tests η cap μ) ∨
    (∃ container ∈ (fittingStage hσ tests η cap).containerList univ L R,
      ((V \ container).card : ℝ) < θ) := by
  rcases Fitting.stage_alternative htests hη hη' hcap hθ L hL R V hR with
    ⟨F, hsub, hsize, word, hword, hfit⟩ | ⟨records, hlen, hwords, hloss⟩
  · exact Or.inl ⟨F, hsub, hsize, _, fittedLaw_mem hσ tests η cap F word hword hfit, hfit⟩
  · exact Or.inr ⟨_, recordedUnion_mem hσ tests η cap records hlen hwords, hloss⟩

/-- The scalar budgets instantiate the fitting dichotomy at an active level. -/
theorem fitting_stage_at_level {p k : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) (hP : Fintype.card P = p)
    {tests : σ → P → ℝ} (htests : ∀ j a, |tests j a| ≤ 1)
    {x : ℝ} (hx : 5000 < x) (hk : 0 < k) (V : Finset P)
    (hsize : (V.card : ℝ) ≤ 2 * (k : ℝ)) :
    let cap := ((10 ^ 24 * k : ℕ) : ℝ)⁻¹
    let η := (inverseEta x)⁻¹
    let stage := fittingStage hσ tests η cap
    (∃ F ⊆ V, (k : ℝ) * lossRate x ≤ F.card ∧
      ∃ μ ∈ stage.cappedLawList (2 * cap) (runBudget p x), Fitting.Fitted F tests η cap μ) ∨
    (∃ container ∈ stage.containerList univ (runBudget p x) (removalBudget x),
      (container.card : ℝ) ≤ Real.exp (x / 2) * (k : ℝ) ∧
        ((V \ container).card : ℝ) < (k : ℝ) * lossRate x) := by
  intro cap η stage
  have hx0 : 0 < x := by linarith
  have hη : 0 < η := inv_pos.mpr (Real.exp_pos _)
  have hcap : 0 < cap := by dsimp only [cap]; positivity
  have hθ : 0 < (k : ℝ) * lossRate x := by unfold lossRate; positivity
  have hrun : 16 * Real.log (Fintype.card P) < (runBudget p x : ℝ) * η ^ 2 := by
    rw [hP]
    exact runBudget_suffices p x
  have hout := fitting_stage_enumerated hσ htests hη (inv_inverseEta_le_half hx0.le)
    hcap.le hθ (runBudget p x) hrun (removalBudget x) V
    (removalBudget_suffices (by linarith) (by positivity) hsize)
  rcases hout with hfit | ⟨container, hmem, hloss⟩
  · exact Or.inl hfit
  · refine Or.inr ⟨container, hmem, ?_, hloss⟩
    exact stage.container_card_le_shrink hx.le le_rfl
      (fun word _ => fittingStage_heavy_le (by positivity : 0 < 10 ^ 24 * k) hσ tests η word) hmem

/-- A single last-stage family covers every admissible list of records and has
both the cardinality and member-size bounds required in §1. -/
theorem fitting_terminal_family {p k L R : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hC : 1 ≤ C) (hx : 5000 < x) (hstop : x ≤ 10000)
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + Real.log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    let cap := ((10 ^ 24 * k : ℕ) : ℝ)⁻¹
    let η := (inverseEta x)⁻¹
    ∃ family : Finset (Finset P),
      logCard family ≤
        24 * C * (inverseEta 10000) ^ 3 * (1 + Real.log (2 * (10000 : ℝ) ^ 2)) *
          (1 + Real.log (p : ℝ)) ^ 2 ∧
      (∀ container ∈ family, (container.card : ℝ) ≤ Real.exp 5000 * (k : ℝ)) ∧
      (∀ records : List (List (Fitting.Instruction σ)), records.length ≤ R →
        (∀ word ∈ records, word.length ≤ L) →
        Fitting.recordedUnion tests η cap records ∈ family) := by
  intro cap η
  let stage := fittingStage hσ tests η cap
  refine ⟨stage.containerList univ L R, stage.logCard_last_containers hp hC hx hstop hL hR,
    ?_, fun records hlen hwords => recordedUnion_mem hσ tests η cap records hlen hwords⟩
  intro container hmem
  exact stage.terminal_card_le hx hstop hR
    (fun word _ => fittingStage_heavy_le (by positivity : 0 < 10 ^ 24 * k) hσ tests η word) hmem

end

end Green39.Transcripts

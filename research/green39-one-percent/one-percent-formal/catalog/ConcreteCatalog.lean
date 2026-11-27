import AssemblyModel
import FitParameters
import FittingBridge

/-! A finite catalog whose entries are decoded from the explicit cyclic fitting runs. -/

open Finset Real
open scoped Classical

namespace Green39.Assembly

noncomputable section

open OnePercent.Fourier

private theorem exists_stop (p : ℕ) : ∃ i, x p i ≤ 5000 := by
  by_cases h : x p 0 ≤ 5000
  · exact ⟨0, h⟩
  · obtain ⟨i, _, hi⟩ := Transcripts.exists_last_active (lt_of_not_ge h)
    exact ⟨i + 1, hi⟩

def stageCount (p : ℕ) : ℕ := Nat.find (exists_stop p)

theorem stageCount_active {p i : ℕ} (hi : i < stageCount p) : 5000 < x p i :=
  lt_of_not_ge (Nat.find_min (exists_stop p) hi)

theorem stageCount_stop (p : ℕ) : x p (stageCount p) ≤ 5000 :=
  Nat.find_spec (exists_stop p)

theorem stageCount_pos {p : ℕ} (h : 5000 < x p 0) : 0 < stageCount p := by
  by_contra! hz
  simpa [Nat.eq_zero_of_le_zero hz, h.not_ge] using stageCount_stop p

theorem stageCount_le (p : ℕ) : (stageCount p : ℝ) ≤ 1 + x p 0 / 5000 := by
  have hx : 0 ≤ x p 0 := by
    unfold x Transcripts.level
    by_cases hp : p = 0
    · simp [hp]
    · apply log_nonneg
      have hk : 0 < p.sqrt := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hp)
      exact (one_le_div (Nat.cast_pos.mpr hk)).mpr (Nat.cast_le.mpr (Nat.sqrt_le_self p))
  cases h : stageCount p with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ i =>
    have hi := stageCount_active (p := p) (i := i) (by omega)
    have hpow : (i : ℝ) < 2 ^ i := by exact_mod_cast (Nat.lt_two_pow_self : i < 2 ^ i)
    unfold x at hi
    rw [Transcripts.level_eq_div_pow, lt_div_iff₀ (by positivity)] at hi
    simp only [Nat.cast_succ]
    change (i : ℝ) + 1 ≤ 1 + Real.log ((p : ℝ) / ↑p.sqrt) / 5000
    linarith

variable {p : ℕ} [NeZero p]

private theorem p_pos (p : ℕ) [NeZero p] : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

private theorem k_pos (p : ℕ) [NeZero p] : 0 < p.sqrt := Nat.sqrt_pos.mpr (p_pos p)

private theorem x_le_initial (p : ℕ) [NeZero p] (i : ℕ) : x p i ≤ x p 0 := by
  apply Transcripts.level_antitone _ (Nat.zero_le i)
  exact log_nonneg ((one_le_div (Nat.cast_pos.mpr (k_pos p))).mpr
    (Nat.cast_le.mpr (Nat.sqrt_le_self p)))

private theorem eta_eq (y : ℝ) : eta y = (Transcripts.inverseEta y)⁻¹ := by
  rw [Transcripts.inv_inverseEta]
  unfold eta
  congr 1
  ring

def fittingCap (p : ℕ) : ℝ := 1 / (10 ^ 24 * (p.sqrt : ℝ))

def fittingWords (p i : ℕ) : ℕ := Fitting.wordBudget p (eta (x p i))

def fittingPeels (p i : ℕ) : ℕ := Fitting.peelBudget (eta (x p i)) (Transcripts.lossRate (x p i))

theorem fittingWords_le (p i : ℕ) : fittingWords p i ≤ Transcripts.runBudget p (x p i) := by
  unfold fittingWords Fitting.wordBudget Transcripts.runBudget
  rw [eta_eq, inv_pow, div_inv_eq_mul]
  exact Nat.add_le_add_right (Nat.floor_le_ceil _) _

theorem fittingPeels_le (p i : ℕ) : fittingPeels p i ≤ Transcripts.removalBudget (x p i) := by
  unfold fittingPeels Fitting.peelBudget Transcripts.removalBudget Transcripts.lossRate
  rw [eta_eq, div_inv_eq_mul, div_div_eq_mul_div, div_one]
  have h := Nat.floor_le_ceil
    (2 * Transcripts.inverseEta (x p i) * Real.log (2 * x p i ^ 2))
  omega

private theorem cyclic_alphabet (p : ℕ) [NeZero p] : Fintype.card (ZMod p × Bool) = 2 * p := by
  simp [Nat.mul_comm]

def cyclicDecoder (p : ℕ) [NeZero p] (i : ℕ) :
    Transcripts.Stage (Law p) (Transcripts.Instruction p) (Law p) (ZMod p) :=
  Transcripts.fittingStage (cyclic_alphabet p) (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p)

/-- Stage zero starts with the full group. Each later list is decoded from the
immediately preceding stage's records, with no dependence on prior containers. -/
def concreteCatalog (p : ℕ) [NeZero p] : Catalog p where
  stages := stageCount p
  containers
    | 0 => {univ}
    | i + 1 => (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i)
  laws i := (cyclicDecoder p i).cappedLawList (2 * fittingCap p) (fittingWords p i)

theorem concreteCatalog_container_mem (p : ℕ) [NeZero p] (i : ℕ)
    (ws : List (List (Fitting.Instruction (ZMod p × Bool))))
    (hlen : ws.length ≤ fittingPeels p i) (hword : ∀ w ∈ ws, w.length ≤ fittingWords p i) :
    Fitting.recordedUnion (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p) ws ∈
      (concreteCatalog p).containers (i + 1) :=
  Transcripts.recordedUnion_mem (cyclic_alphabet p) _ _ _ ws hlen hword

/-- Every listed container, including a terminal one, is the union decoded
from a single stage's records. -/
theorem concreteCatalog_mem_containers_iff (p : ℕ) [NeZero p] (i : ℕ) (P : Points p) :
    P ∈ (concreteCatalog p).containers (i + 1) ↔
      ∃ ws : List (List (Fitting.Instruction (ZMod p × Bool))), ws.length ≤ fittingPeels p i ∧
        (∀ w ∈ ws, w.length ≤ fittingWords p i) ∧
        P = Fitting.recordedUnion (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p) ws := by
  constructor
  · intro hP
    change P ∈ (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i) at hP
    obtain ⟨records, hrecords, rfl⟩ := mem_image.mp hP
    obtain ⟨hlen, hwords⟩ := Transcripts.mem_words.mp hrecords
    let decodeWord (w : List (Transcripts.Instruction p)) :=
      (w.map (Transcripts.instructionEquiv (cyclic_alphabet p)).symm).reverse
    let ws := records.map decodeWord
    refine ⟨ws, by simpa only [ws, List.length_map] using hlen, ?_, ?_⟩
    · intro w hw
      obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hw
      simpa only [decodeWord, List.length_reverse, List.length_map] using
        (Transcripts.mem_words.mp (hwords record hrecord)).1
    · have hcomp : Transcripts.encodeFittingWord (cyclic_alphabet p) ∘ decodeWord = id := by
        funext word
        simp [Transcripts.encodeFittingWord, decodeWord, List.map_map, Function.comp_def]
      have hmap : ws.map (Transcripts.encodeFittingWord (cyclic_alphabet p)) = records := by
        simp only [ws, List.map_map, hcomp, List.map_id]
      calc
        (cyclicDecoder p i).outputContainer records =
            (cyclicDecoder p i).outputContainer (ws.map (Transcripts.encodeFittingWord (cyclic_alphabet p))) :=
          congrArg (cyclicDecoder p i).outputContainer hmap.symm
        _ = _ := Transcripts.fittingStage_outputContainer_eq (cyclic_alphabet p) _ _ _ ws
  · rintro ⟨ws, hlen, hword, rfl⟩
    exact concreteCatalog_container_mem p i ws hlen hword

private theorem concreteCatalog_law_mem (i : ℕ) (w : List (Fitting.Instruction (ZMod p × Bool)))
    (hlen : w.length ≤ fittingWords p i)
    (hcap : Transcripts.IsCappedLaw (2 * fittingCap p)
      (Fitting.fittedLaw (eta (x p i)) (fittingCap p) w)) :
    Fitting.fittedLaw (eta (x p i)) (fittingCap p) w ∈ (concreteCatalog p).laws i := by
  apply (Transcripts.Stage.mem_cappedLawList _).mpr
  refine ⟨hcap, Transcripts.encodeFittingWord (cyclic_alphabet p) w, ?_, ?_⟩
  · simpa only [Transcripts.encodeFittingWord_length] using hlen
  · unfold cyclicDecoder Transcripts.Stage.outputLaw
    rw [Transcripts.fittingStage_replay_eq]
    rfl

theorem concreteCatalog_spec (p : ℕ) [NeZero p] : StageSpec (concreteCatalog p) := by
  refine ⟨by simp [concreteCatalog], fun _ => stageCount_active, stageCount_stop p, ?_, ?_, ?_⟩
  · intro i hi P hP
    cases i with
    | zero =>
      have hP' : P = univ := by simpa [concreteCatalog] using hP
      subst P
      have hk : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr (k_pos p)
      rw [card_univ, ZMod.card, x, Transcripts.level,
        exp_log (div_pos (Nat.cast_pos.mpr (p_pos p)) hk)]
      exact le_of_eq (by field_simp)
    | succ i =>
      have hx := stageCount_active (p := p) (i := i) (by
        change i + 1 ≤ stageCount p at hi
        omega)
      have hcap : fittingCap p = ((10 ^ 24 * p.sqrt : ℕ) : ℝ)⁻¹ := by
        norm_num [fittingCap, one_div]
      change P ∈ (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i) at hP
      have h := (cyclicDecoder p i).container_card_le_shrink hx.le (fittingPeels_le p i)
        (k := p.sqrt) (fun word _ => by
          unfold cyclicDecoder
          rw [hcap]
          exact Transcripts.fittingStage_heavy_le (Nat.mul_pos (by decide) (k_pos p))
            (cyclic_alphabet p) _ _ word) hP
      simpa only [x, Transcripts.level, mul_comm] using h
  · intro i _ μ hμ
    have h := ((Transcripts.Stage.mem_cappedLawList _).mp hμ).1
    exact ⟨h.1.1, h.1.2, fun z => by simpa only [fittingCap, mul_one_div] using h.2 z⟩
  · intro i hi _ _ V _ _ hV
    have hx := stageCount_active hi
    have hk : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr (k_pos p)
    have hη : 0 < eta (x p i) := exp_pos _
    have hη' : eta (x p i) ≤ 1 / 2 := by
      rw [eta_eq]
      exact Transcripts.inv_inverseEta_le_half (by linarith)
    have hξ : 0 < Transcripts.lossRate (x p i) := by
      unfold Transcripts.lossRate
      exact one_div_pos.mpr (sq_pos_of_pos (by linarith))
    rcases Fitting.cyclic_stage_explicit V hk hV hη hη' hξ (by norm_num : (0 : ℝ) < 10 ^ 24) with
      ⟨F, hsub, hcard, w, hw, hsum, hcap, hfit⟩ | ⟨ws, hlen, hwords, _, hcut⟩
    · have hF : F.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hξ hk).trans_le hcard)
      refine Or.inl ⟨F, hsub, by simpa only [mul_comm] using hcard, _,
        concreteCatalog_law_mem i w hw ⟨⟨fun z => (hcap z).1, hsum⟩, fun z => (hcap z).2⟩,
        (fourierFit_iff_uniformLaw _ _ hF _).mpr ?_⟩
      have hu : uniformLaw F = fun z => (Fitting.uniformOn F z : ℂ) := by
        funext z
        by_cases hz : z ∈ F <;> simp [uniformLaw, indicator, Fitting.uniformOn, hz, one_div]
      rw [hu]
      exact hfit
    · exact Or.inr ⟨_, concreteCatalog_container_mem p i ws hlen hwords,
        by simpa only [fittingCap, mul_comm] using hcut.le⟩

theorem concreteCatalog_card_laws (p : ℕ) [NeZero p] (i : ℕ) :
    ((concreteCatalog p).laws i).card ≤ Transcripts.wordCount (4 * p + 1) (fittingWords p i) := by
  change ((cyclicDecoder p i).cappedLawList _ _).card ≤ _
  refine (card_filter_le _ _).trans ?_
  simpa only [card_univ, Transcripts.card_instruction] using
    (cyclicDecoder p i).card_lawList_le univ (fittingWords p i)

theorem concreteCatalog_card_containers (p : ℕ) [NeZero p] (i : ℕ) :
    ((concreteCatalog p).containers (i + 1)).card ≤
      Transcripts.wordCount (Transcripts.wordCount (4 * p + 1) (fittingWords p i))
        (fittingPeels p i) := by
  simpa only [concreteCatalog, card_univ, Transcripts.card_instruction] using
    (cyclicDecoder p i).card_containerList_le univ (fittingWords p i) (fittingPeels p i)

private theorem fittingWords_real_le (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    (fittingWords p i : ℝ) ≤ 18 * Transcripts.inverseEta (x p i) ^ 2 * (1 + log (p : ℝ)) :=
  (Nat.cast_le.mpr (fittingWords_le p i)).trans
    (Transcripts.runBudget_le (p_pos p) (by linarith [stageCount_active hi]))

def lawExponent (p : ℕ) : ℝ :=
  7 * 18 * exp 2000 * (4 * (p.sqrt : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2

def containerExponent (p : ℕ) : ℝ :=
  48 * 18 * exp 3000 * (4 * (p.sqrt : ℝ)) ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
    (1 + log (1 + log (p : ℝ)))

def terminalCoefficient : ℝ :=
  24 * 18 * Transcripts.inverseEta 10000 ^ 3 * (1 + log (2 * (10000 : ℝ) ^ 2))

theorem concreteCatalog_log_laws (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).laws i) ≤ lawExponent p := by
  exact (cyclicDecoder p i).logCard_cappedLaws_power (p_pos p) (k_pos p) (Nat.lt_succ_sqrt' p)
    (by norm_num : (1 : ℝ) ≤ 18) (stageCount_active hi) (x_le_initial p i)
    (fittingWords_real_le p hi)

theorem concreteCatalog_log_containers (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).containers (i + 1)) ≤ containerExponent p := by
  exact (cyclicDecoder p i).logCard_containers_power (p_pos p) (k_pos p) (Nat.lt_succ_sqrt' p)
    (by norm_num : (1 : ℝ) ≤ 18) (stageCount_active hi) (x_le_initial p i)
    (fittingWords_real_le p hi) (fittingPeels_le p i)

theorem concreteCatalog_log_terminal (p : ℕ) [NeZero p] (h : 0 < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).containers (concreteCatalog p).stages) ≤
      terminalCoefficient * (1 + log (p : ℝ)) ^ 2 := by
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  have hactive : i < stageCount p := by omega
  have hstop : x p (i + 1) ≤ 5000 := by
    simpa only [hi, Nat.succ_eq_add_one] using stageCount_stop p
  have hlast := (Transcripts.last_level_bounds (stageCount_active hactive) hstop).2
  change Transcripts.logCard ((concreteCatalog p).containers (stageCount p)) ≤ _
  rw [hi]
  exact (cyclicDecoder p i).logCard_last_containers (p_pos p) (by norm_num : (1 : ℝ) ≤ 18)
    (stageCount_active hactive) hlast (fittingWords_real_le p hactive) (fittingPeels_le p i)

theorem concreteCatalog_log_allLaws (p : ℕ) [NeZero p] :
    Transcripts.logCard ((range (concreteCatalog p).stages).biUnion (concreteCatalog p).laws) ≤
      log (1 + (stageCount p : ℝ)) + lawExponent p := by
  have hnonneg : 0 ≤ lawExponent p := by unfold lawExponent; positivity
  exact (Transcripts.logCard_biUnion_le _ _ hnonneg
    (fun _ hi => concreteCatalog_log_laws p (mem_range.mp hi))).trans_eq
    (by rw [card_range])

private theorem card_le_exp_of_logCard {α : Type*} {s : Finset α} {a : ℝ}
    (h : Transcripts.logCard s ≤ a) : (s.card : ℝ) ≤ exp a := by
  have h' := (log_le_iff_le_exp (by positivity : 0 < 1 + (s.card : ℝ))).mp h
  linarith

theorem concreteCatalog_sum_card_products (p : ℕ) [NeZero p] :
    (∑ i ∈ range (concreteCatalog p).stages,
      (((concreteCatalog p).containers i).card : ℝ) * ((concreteCatalog p).laws i).card) ≤
      (stageCount p : ℝ) * exp (containerExponent p + lawExponent p) := by
  have hp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast p_pos p)
  have he : 0 ≤ containerExponent p := by
    have hlog : 0 ≤ log (1 + log (p : ℝ)) := log_nonneg (by linarith)
    unfold containerExponent
    positivity
  calc
    _ ≤ ∑ _ ∈ range (concreteCatalog p).stages, exp (containerExponent p + lawExponent p) := by
      apply sum_le_sum
      intro i hi
      have hL := card_le_exp_of_logCard (concreteCatalog_log_laws p (mem_range.mp hi))
      have hC : (((concreteCatalog p).containers i).card : ℝ) ≤ exp (containerExponent p) := by
        cases i with
        | zero => simpa [concreteCatalog] using one_le_exp he
        | succ i =>
          apply card_le_exp_of_logCard
          apply concreteCatalog_log_containers p
          have h := mem_range.mp hi
          change i + 1 < stageCount p at h
          omega
      rw [exp_add]
      exact mul_le_mul hC hL (Nat.cast_nonneg _) (exp_pos _).le
    _ = _ := by simp [concreteCatalog, nsmul_eq_mul]

end

end Green39.Assembly

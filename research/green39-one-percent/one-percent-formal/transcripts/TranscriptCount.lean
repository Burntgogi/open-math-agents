import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Finite decoding and counting for the restarted runs in §3. -/

namespace Green39.Transcripts

open Finset

/-- The four signed tests for each frequency, plus the state-dependent heavy-set test. -/
abbrev Instruction (p : ℕ) := (Fin 4 × Fin p) ⊕ Unit

theorem card_instruction (p : ℕ) : Fintype.card (Instruction p) = 4 * p + 1 := by
  simp

variable {A : Type*} [DecidableEq A]

/-- All ordered words of length at most the budget in the given finite alphabet. -/
def words (alphabet : Finset A) : ℕ → Finset (List A)
  | 0 => {[]}
  | n + 1 => insert [] ((alphabet ×ˢ words alphabet n).image fun aw => aw.1 :: aw.2)

theorem mem_words {alphabet : Finset A} {n : ℕ} {w : List A} :
    w ∈ words alphabet n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp [words, ih, forall_eq_or_imp, and_assoc, and_left_comm, and_comm]

/-- The exact number of words, including the empty word. -/
def wordCount (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + a * wordCount a n

theorem wordCount_eq_sum (a n : ℕ) :
    wordCount a n = ∑ i ∈ range (n + 1), a ^ i := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    rw [wordCount, ih, sum_range_succ' (fun i => a ^ i) (n + 1), mul_sum, pow_zero]
    simp only [pow_succ', Nat.add_comm 1]

theorem card_words (alphabet : Finset A) (n : ℕ) :
    (words alphabet n).card = wordCount alphabet.card n := by
  induction n with
  | zero => simp [words, wordCount]
  | succ n ih =>
    have hnil : [] ∉ (alphabet ×ˢ words alphabet n).image
        (fun aw : A × List A => aw.1 :: aw.2) := by simp
    have hinj : Function.Injective (fun aw : A × List A => aw.1 :: aw.2) := by
      rintro ⟨a, w⟩ ⟨b, v⟩ h
      simpa using h
    rw [words, card_insert_of_notMem hnil, card_image_of_injective _ hinj,
      card_product, ih, wordCount, Nat.add_comm]

theorem wordCount_le (a n : ℕ) : wordCount a n ≤ (a + 1) ^ n := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    rw [wordCount]
    calc
      1 + a * wordCount a n ≤ (a + 1) ^ n + a * (a + 1) ^ n :=
        Nat.add_le_add (Nat.one_le_pow _ _ (by omega)) (Nat.mul_le_mul_left a ih)
      _ = (a + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- A fixed stage can replay a run from its reset state. The step reads the current
state, so the heavy-set instruction needs no additional symbol for the set. -/
structure Stage (State A Law Point : Type*) where
  reset : State
  step : State → A → State
  law : State → Law
  heavy : State → Finset Point

variable {State Law Point : Type*}

def Stage.replay (stage : Stage State A Law Point) (record : List A) : State :=
  record.foldl stage.step stage.reset

def Stage.outputLaw (stage : Stage State A Law Point) (record : List A) : Law :=
  stage.law (stage.replay record)

def Stage.outputHeavy (stage : Stage State A Law Point) (record : List A) : Finset Point :=
  stage.heavy (stage.replay record)

variable [DecidableEq Point]

/-- All records in the outer word are decoded from the same reset. -/
def Stage.outputContainer (stage : Stage State A Law Point) : List (List A) → Finset Point
  | [] => ∅
  | record :: rest => stage.outputHeavy record ∪ stage.outputContainer rest

omit [DecidableEq A] [DecidableEq Point] in
/-- A run starting in the prescribed reset state has the replayed state. -/
theorem Stage.replay_eq_of_reset (stage : Stage State A Law Point)
    {start : State} (h : start = stage.reset) (record : List A) :
    record.foldl stage.step start = stage.replay record := by
  subst start
  rfl

omit [DecidableEq A] [DecidableEq Point] in
/-- Any two input histories selecting the same current record have the same output,
provided both start in the prescribed reset state. -/
theorem Stage.history_independent (stage : Stage State A Law Point)
    {History : Type*} (start : History → State) (h : ∀ history, start history = stage.reset)
    (left right : History) (record : List A) :
    record.foldl stage.step (start left) = record.foldl stage.step (start right) := by
  rw [h left, h right]

omit [DecidableEq A] in
/-- The container formed by an implementation that resets each run belongs to the same
stage-only decoding, even if the implementation uses an arbitrary start function. -/
theorem Stage.container_eq_of_reset (stage : Stage State A Law Point)
    (start : List A → State) (h : ∀ record, start record = stage.reset)
    (records : List (List A)) :
    (records.map (fun record => stage.heavy (record.foldl stage.step (start record)))).foldr
        (· ∪ ·) ∅ = stage.outputContainer records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    simp only [List.map_cons, List.foldr_cons, Stage.outputContainer]
    rw [ih, stage.replay_eq_of_reset (h record)]
    rfl

def Stage.lawList [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget : ℕ) : Finset Law :=
  (words alphabet runBudget).image stage.outputLaw

def Stage.containerList (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) : Finset (Finset Point) :=
  (words (words alphabet runBudget) removalBudget).image stage.outputContainer

omit [DecidableEq Point] in
theorem Stage.outputLaw_mem [DecidableEq Law] (stage : Stage State A Law Point)
    {alphabet : Finset A} {runBudget : ℕ} {record : List A}
    (hlen : record.length ≤ runBudget) (hsym : ∀ a ∈ record, a ∈ alphabet) :
    stage.outputLaw record ∈ stage.lawList alphabet runBudget :=
  mem_image_of_mem _ (mem_words.mpr ⟨hlen, hsym⟩)

theorem Stage.outputContainer_mem (stage : Stage State A Law Point)
    {alphabet : Finset A} {runBudget removalBudget : ℕ} {records : List (List A)}
    (hlen : records.length ≤ removalBudget)
    (hword : ∀ record ∈ records, record.length ≤ runBudget ∧ ∀ a ∈ record, a ∈ alphabet) :
    stage.outputContainer records ∈ stage.containerList alphabet runBudget removalBudget :=
  mem_image_of_mem _ (mem_words.mpr ⟨hlen, fun record hr => mem_words.mpr (hword record hr)⟩)

/-- In particular the empty union appears even if the removal budget is zero. -/
theorem Stage.empty_mem_containerList (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) :
    ∅ ∈ stage.containerList alphabet runBudget removalBudget := by
  simpa [Stage.outputContainer] using stage.outputContainer_mem
    (alphabet := alphabet) (runBudget := runBudget) (removalBudget := removalBudget)
    (records := []) (by simp) (by simp)

/-- One fixed list covers the implementation's output for every prior history.
The selected words may depend on the history, but their decoding never does. -/
theorem Stage.container_mem_of_history (stage : Stage State A Law Point)
    {History : Type*} (records : History → List (List A)) (start : History → List A → State)
    (hreset : ∀ history record, start history record = stage.reset)
    (alphabet : Finset A) (runBudget removalBudget : ℕ)
    (hlen : ∀ history, (records history).length ≤ removalBudget)
    (hword : ∀ history record, record ∈ records history →
      record.length ≤ runBudget ∧ ∀ a ∈ record, a ∈ alphabet)
    (history : History) :
    ((records history).map (fun record =>
      stage.heavy (record.foldl stage.step (start history record)))).foldr (· ∪ ·) ∅ ∈
      stage.containerList alphabet runBudget removalBudget := by
  rw [stage.container_eq_of_reset (start history) (hreset history)]
  exact stage.outputContainer_mem (hlen history) (hword history)

omit [DecidableEq Point] in
theorem Stage.card_lawList_le [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget : ℕ) :
    (stage.lawList alphabet runBudget).card ≤ wordCount alphabet.card runBudget :=
  card_words alphabet runBudget ▸ card_image_le

theorem Stage.card_containerList_le (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) :
    (stage.containerList alphabet runBudget removalBudget).card ≤
      wordCount (wordCount alphabet.card runBudget) removalBudget := by
  unfold Stage.containerList
  exact card_image_le.trans (by rw [card_words, card_words])

omit [DecidableEq A] in
theorem Stage.card_outputContainer_le (stage : Stage State A Law Point)
    (records : List (List A)) (heavyBudget : ℕ)
    (h : ∀ record ∈ records, (stage.outputHeavy record).card ≤ heavyBudget) :
    (stage.outputContainer records).card ≤ records.length * heavyBudget := by
  induction records with
  | nil => simp [Stage.outputContainer]
  | cons record rest ih =>
    rw [Stage.outputContainer, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (card_union_le _ _).trans (by
      have hfirst := h record List.mem_cons_self
      have hrest := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
      omega)

theorem Stage.card_mem_containerList_le (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget heavyBudget : ℕ)
    (h : ∀ record ∈ words alphabet runBudget, (stage.outputHeavy record).card ≤ heavyBudget)
    {container : Finset Point} (hmem : container ∈ stage.containerList alphabet runBudget removalBudget) :
    container.card ≤ removalBudget * heavyBudget := by
  obtain ⟨records, hrecords, rfl⟩ := mem_image.mp hmem
  obtain ⟨hlen, hwords⟩ := mem_words.mp hrecords
  exact (stage.card_outputContainer_le records heavyBudget
    (fun record hr => h record (hwords record hr))).trans (Nat.mul_le_mul_right _ hlen)

end Green39.Transcripts

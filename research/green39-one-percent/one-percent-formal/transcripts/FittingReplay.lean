import TranscriptBounds

/-! The interface between the fitting procedure and its target-independent descriptions.
The caller supplies the public tests and the fitting procedure's tilt and trim functions. -/

namespace Green39.Transcripts

open Finset

noncomputable section

variable {P : Type*} [Fintype P]

def IsLaw (m : P → ℝ) : Prop := (∀ a, 0 ≤ m a) ∧ ∑ a, m a = 1

def IsCappedLaw (cap : ℝ) (m : P → ℝ) : Prop := IsLaw m ∧ ∀ a, m a ≤ cap

def uniformState : P → ℝ := fun _ => (Fintype.card P : ℝ)⁻¹

theorem uniformState_isLaw [Nonempty P] : IsLaw (uniformState : P → ℝ) := by
  have hcard : (Fintype.card P : ℝ) ≠ 0 := by positivity
  constructor
  · intro a
    unfold uniformState
    positivity
  · simp [uniformState, sum_const, nsmul_eq_mul, hcard]

def heavyAt (cap : ℝ) (m : P → ℝ) : Finset P := by
  classical
  exact univ.filter fun a => cap < m a

theorem mem_heavyAt {cap : ℝ} {m : P → ℝ} {a : P} :
    a ∈ heavyAt cap m ↔ cap < m a := by
  classical
  simp [heavyAt]

theorem heavyAt_card_le {B : ℕ} {m : P → ℝ} (hB : 0 < B) (hm : IsLaw m) :
    (heavyAt (B : ℝ)⁻¹ m).card ≤ B := by
  let J := heavyAt (B : ℝ)⁻¹ m
  have hB' : (0 : ℝ) < B := by positivity
  have hsum : (J.card : ℝ) * (B : ℝ)⁻¹ ≤ 1 := calc
    _ = ∑ _a ∈ J, (B : ℝ)⁻¹ := by simp [sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ J, m a := sum_le_sum fun _ ha => (mem_heavyAt.mp ha).le
    _ ≤ ∑ a, m a := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => hm.1 a)
    _ = 1 := hm.2
  rw [← div_eq_mul_inv, div_le_iff₀ hB', one_mul] at hsum
  exact_mod_cast hsum

/-- The heavy test is decoded from the current law. The initial law is uniform
and the signed tests, tilt, cap, and trim are fixed public stage data. -/
def uniformStage {p : ℕ} (cap : ℝ) (signedTests : Fin 4 × Fin p → P → ℝ)
    (tilt : (P → ℝ) → (P → ℝ) → P → ℝ) (trim : Finset P → (P → ℝ) → P → ℝ) :
    Stage (P → ℝ) (Instruction p) (P → ℝ) P := by
  classical
  exact {
    reset := uniformState
    step := fun m instruction => tilt m (match instruction with
      | .inl test => signedTests test
      | .inr _ => fun a => if a ∈ heavyAt cap m then -1 else 0)
    law := fun m => trim (heavyAt cap m) m
    heavy := heavyAt cap
  }

omit [Fintype P] in
private theorem foldl_preserves {Q : Type*} {A : Type*} (step : Q → A → Q)
    (invariant : Q → Prop) (hs : ∀ q a, invariant q → invariant (step q a))
    (record : List A) (start : Q) (hstart : invariant start) :
    invariant (record.foldl step start) := by
  induction record generalizing start with
  | nil => exact hstart
  | cons a record ih => exact ih (step start a) (hs start a hstart)

/-- A tilt preserving probability laws gives the heavy-set size bound for every
word in the encoding, including words the target-dependent algorithm would never select. -/
theorem uniformStage_heavy_le {p B : ℕ} [Nonempty P] (hB : 0 < B)
    (signedTests : Fin 4 × Fin p → P → ℝ)
    (tilt : (P → ℝ) → (P → ℝ) → P → ℝ) (trim : Finset P → (P → ℝ) → P → ℝ)
    (htilt : ∀ m f, IsLaw m → IsLaw (tilt m f)) (record : List (Instruction p)) :
    ((uniformStage (B : ℝ)⁻¹ signedTests tilt trim).outputHeavy record).card ≤ B := by
  classical
  let stage := uniformStage (B : ℝ)⁻¹ signedTests tilt trim
  apply heavyAt_card_le hB
  apply foldl_preserves stage.step IsLaw _ record stage.reset uniformState_isLaw
  intro m instruction hm
  cases instruction <;> exact htilt m _ hm

/-- Filtering the over-enumeration by the cap and the law axioms gives a list of
genuine capped probability laws. -/
def Stage.cappedLawList {S : Type*} {p : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) (cap : ℝ) (L : ℕ) : Finset (P → ℝ) := by
  classical
  exact (stage.lawList univ L).filter (IsCappedLaw cap)

theorem Stage.mem_cappedLawList {S : Type*} {p : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) {cap : ℝ} {L : ℕ} {m : P → ℝ} :
    m ∈ stage.cappedLawList cap L ↔
      IsCappedLaw cap m ∧ ∃ record : List (Instruction p), record.length ≤ L ∧
        stage.outputLaw record = m := by
  classical
  simp only [Stage.cappedLawList, Stage.lawList, mem_filter, mem_image, mem_words,
    mem_univ, implies_true, and_true]
  exact and_comm

theorem Stage.logCard_cappedLaws_power {S : Type*} {p k L : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) {C x cap : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ Real.log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + Real.log (p : ℝ))) :
    logCard (stage.cappedLawList cap L) ≤
      7 * C * Real.exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + Real.log (p : ℝ)) ^ 2 := by
  classical
  exact (logCard_mono (filter_subset _ _)).trans
    (stage.logCard_laws_power hp hk hsqrt hC hx hupper hL)

/-- The joint law family used in §4 contains only capped probability laws. It
inherits the all-stage logarithmic budget from the unfiltered descriptions. -/
theorem logCard_all_cappedLaws {S : Type*} {p k n : ℕ}
    (stage : ℕ → Stage S (Instruction p) (P → ℝ) P) (cap : ℝ) (L : ℕ → ℕ) {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (Real.log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (Real.log ((p : ℝ) / k)) i) ^ 2 * (1 + Real.log (p : ℝ))) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).cappedLawList cap (L i))) ≤
      Real.log (1 + (n + 1 : ℕ)) +
        7 * C * Real.exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + Real.log (p : ℝ)) ^ 2 := by
  classical
  refine (logCard_mono ?_).trans (logCard_all_laws stage L hp hk hsqrt hC hactive hL)
  intro law hlaw
  obtain ⟨i, hi, hmem⟩ := mem_biUnion.mp hlaw
  exact mem_biUnion.mpr ⟨i, hi, (mem_filter.mp hmem).1⟩

end

end Green39.Transcripts

import SliceConcentration

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

def incProb (s : Finset α) (k : ℕ) (t : Finset α) : ℝ :=
  (((s.powersetCard k).filter (fun A ↦ t ⊆ A)).card : ℝ) / (s.powersetCard k).card

theorem inc_empty {s : Finset α} {k : ℕ} (hk : k ≤ s.card) :
    incProb s k ∅ = 1 := by
  simp [incProb, (Nat.choose_pos hk).ne']

private theorem count_insert (s t : Finset α) (k : ℕ) {x : α} (hx : x ∈ s) (ht : x ∉ t) :
    ((s.powersetCard (k+1)).filter (fun A ↦ insert x t ⊆ A)).card =
      (((s.erase x).powersetCard k).filter (fun A ↦ t ⊆ A)).card := by
  apply Finset.card_bij (fun A _ ↦ A.erase x)
  · intro A h
    obtain ⟨ha, hxt⟩ := Finset.mem_filter.mp h
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨hxA, htA⟩ := Finset.insert_subset_iff.mp hxt
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase x hs,
      by simp [Finset.card_erase_of_mem hxA, hc]⟩, fun y hy ↦
      Finset.mem_erase.mpr ⟨fun he ↦ ht (he ▸ hy), htA hy⟩⟩
  · intro A hA B hB he
    have hmem (C : Finset α) (hC : C ∈ (s.powersetCard (k+1)).filter (fun D ↦ insert x t ⊆ D)) :
        x ∈ C := (Finset.mem_filter.mp hC).2 (Finset.mem_insert_self _ _)
    simpa [Finset.insert_erase (hmem _ hA), Finset.insert_erase (hmem _ hB)] using
      congrArg (insert x) he
  · intro B hB
    obtain ⟨hb, htB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hb
    have hn : x ∉ B := fun h ↦ Finset.notMem_erase x s (hs h)
    exact ⟨insert x B, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hx, hs.trans (Finset.erase_subset _ _)⟩,
       by simp [Finset.card_insert_of_notMem hn, hc]⟩, Finset.insert_subset_insert _ htB⟩,
      Finset.erase_insert hn⟩

theorem inc_insert {s t : Finset α} {k : ℕ} {x : α}
    (hk : k+1 ≤ s.card) (hx : x ∈ s) (ht : x ∉ t) :
    incProb s (k+1) (insert x t) =
      ((k+1 : ℕ) : ℝ) / s.card * incProb (s.erase x) k t := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hx)
  have hk' : k ≤ n := by omega
  have h : (n+1 : ℕ) * n.choose k = (n+1).choose (k+1) * (k+1) := Nat.add_one_mul_choose_eq n k
  unfold incProb
  rw [count_insert s t k hx ht, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_erase_of_mem hx, hn, Nat.succ_sub_one]
  have h' : ((n+1 : ℕ) : ℝ) * n.choose k = ((n+1).choose (k+1) : ℝ) * (k+1 : ℕ) := by exact_mod_cast h
  have h1 := Nat.choose_pos hk'
  have h2 := Nat.choose_pos (Nat.succ_le_succ hk')
  rw [div_mul_div_comm, div_eq_div_iff (by exact_mod_cast h2.ne') (by positivity)]
  push_cast at h' ⊢
  linear_combination (↑(((s.erase x).powersetCard k).filter (fun A ↦ t ⊆ A)).card : ℝ) * h'

theorem inc_singleton {s : Finset α} {k : ℕ} (hk : k ≤ s.card) {x : α} (hx : x ∈ s) :
    incProb s k {x} = (k : ℝ)/s.card := by
  cases k with
  | zero => simp [incProb, Finset.powersetCard_zero]
  | succ k =>
    rw [← Finset.insert_empty (a := x), inc_insert hk hx (Finset.notMem_empty _),
      inc_empty (by rw [Finset.card_erase_of_mem hx]; omega), mul_one]

/-- Joint inclusion probabilities are bounded by independent Bernoulli inclusion. -/
theorem inc_le_pow {s t : Finset α} {k : ℕ} (hk : k ≤ s.card) (ht : t ⊆ s) :
    incProb s k t ≤ ((k : ℝ)/s.card)^t.card := by
  induction t using Finset.induction_on generalizing s k with
  | empty => simp [inc_empty hk]
  | @insert x t hxt ih =>
    obtain ⟨hx, hts⟩ := Finset.insert_subset_iff.mp ht
    cases k with
    | zero => simp [incProb, Finset.powersetCard_zero]
    | succ k =>
      have hcard := Finset.card_erase_of_mem hx
      have hk' : k ≤ (s.erase x).card := by omega
      have hts' : t ⊆ s.erase x := fun y hy ↦ Finset.mem_erase.mpr
        ⟨fun he ↦ hxt (he ▸ hy), hts hy⟩
      have hratio : (k : ℝ)/(s.erase x).card ≤ ((k+1 : ℕ) : ℝ)/s.card := by
        by_cases he : (s.erase x).card = 0
        · simp [he]; positivity
        have hp : 0 < ((s.erase x).card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he
        have hs : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨x,hx⟩
        have hsc : s.card = (s.erase x).card + 1 := by omega
        rw [div_le_div_iff₀ hp hs, hsc, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
        have hk'' : (k : ℝ) ≤ (s.erase x).card := by exact_mod_cast hk'
        nlinarith
      rw [inc_insert hk hx hxt, Finset.card_insert_of_notMem hxt, pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right ((ih hk' hts').trans (pow_le_pow_left₀
        (by positivity) hratio _)) (by positivity)

end
end Green39.Smooth

import BlueRecovery
import OldStableMass

/-! Sum the recovery over all good old integers in finitely many contracted
strips. Membership in a strip is recovered from the old integer itself. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells
noncomputable section
open Classical

theorem good_properties {C : Finset ℕ} (hp : ∀ p ∈ C, p.Prime)
    {a b δ : ℝ} {e : ℕ → ℝ} {m : ℕ} (hm : m ∈ goodWindow C a b δ e) :
    m.primeFactors ⊆ C ∧ (∏ p ∈ m.primeFactors, p) = m ∧
      (∑ p ∈ m.primeFactors, e p) ≤ δ ∧ a < log m ∧ log m ≤ b := by
  obtain ⟨hw,hn⟩ := mem_sdiff.mp hm
  obtain ⟨ha,hl,hr⟩ := mem_oldWindow.mp hw
  have hgood : ¬ ((∃ p ∈ C, p^2 ∣ m) ∨ δ ≤ ∑ p ∈ C with p ∣ m, e p) :=
    fun h => hn (mem_filter.mpr ⟨hw,h⟩)
  have hs : m.primeFactors ⊆ C := fun p h => Nat.mem_factoredNumbers'.mp ha p
    (Nat.prime_of_mem_primeFactors h) (Nat.dvd_of_mem_primeFactors h)
  have eq : C.filter (· ∣ m) = m.primeFactors := by
    ext p; simp only [mem_filter,Nat.mem_primeFactors]
    exact ⟨fun h => ⟨hp p h.1,h.2,ha.1⟩,fun h => ⟨hs (Nat.mem_primeFactors.mpr h),h.2.1⟩⟩
  have sq : Squarefree m := Nat.squarefree_iff_prime_squarefree.mpr (fun p hp' hd => by
    have h := Nat.mem_factoredNumbers'.mp ha p hp' (dvd_trans (dvd_mul_right p p) hd)
    exact hgood (.inl ⟨p,h,by simpa [pow_two] using hd⟩))
  exact ⟨hs,Nat.prod_primeFactors_of_squarefree sq,by
    rw [← eq]; exact le_of_not_ge (fun h => hgood (.inr h)),hl,hr⟩

/-- Weighted sum of actual old good masses over the contracted strips
lower-bounds the new blue density, with arbitrary tolerance after freezing
the old data. Each new integer at each cofactor is counted at most once. -/
theorem blue_bin_recovery {C : Finset ℕ} (hp : ∀ p ∈ C, p.Prime) {b x δ : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (J : Finset ℕ) (hJ : ∀ j ∈ J, 0 < j)
    (e : ℕ → ℝ) (he : ∀ p ∈ C, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (k : ℕ) {w : ℝ} (hw : 0 < w)
    (sep : ∀ᶠ t : ℝ in atTop, Disjoint (bands b t C) (smoothLabels k (exp (t*w))))
    {u : ℕ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, let t := log n/x
      (∑ j ∈ J, recMass (goodWindow C (x-j-1+δ) (x-j-δ) δ e)*smoothKernel k w hw (j+1)) - ε ≤
        density (bands b t C ∪ smoothLabels k (exp (t*w))) n u := by
  let bin (j : ℕ) := goodWindow C (x-j-1+δ) (x-j-δ) δ e
  let A := J.sigma bin
  let g (s : Sigma (fun _ : ℕ => ℕ)) := s.2.primeFactors
  let prop (s : Sigma (fun _ : ℕ => ℕ)) (hs : s ∈ A) := good_properties hp (mem_sigma.mp hs).2
  have inj : Set.InjOn g A := by
    rintro ⟨j,m⟩ h1 ⟨l,n⟩ h2 eq
    have a := prop _ h1
    have d := prop _ h2
    obtain rfl : m=n := a.2.1.symm.trans ((congrArg (fun T : Finset ℕ => ∏ p ∈ T, p) eq).trans d.2.1)
    have same : j=l := by
      rcases lt_trichotomy j l with h|h|h
      · have hl : (j:ℝ)+1 ≤ l := by exact_mod_cast h
        have h1' : x-j-1+δ < log m := a.2.2.2.1
        have h2' : log m ≤ x-l-δ := d.2.2.2.2
        linarith
      · exact h
      · have hl : (l:ℝ)+1 ≤ j := by exact_mod_cast h
        have h1' : x-l-1+δ < log m := d.2.2.2.1
        have h2' : log m ≤ x-j-δ := a.2.2.2.2
        linarith
    cases same; rfl
  let G := A.image g
  let source (S : Finset ℕ) := if h : ∃ s ∈ A, g s=S then h.choose else ⟨0,0⟩
  have inv {s} (hs : s ∈ A) : source (g s) = s := by
    have h : ∃ q ∈ A, g q=g s := ⟨_,hs,rfl⟩
    exact (dif_pos h).trans (inj h.choose_spec.1 hs h.choose_spec.2)
  have member {S} (hS : S ∈ G) : source S ∈ A ∧ g (source S)=S := by
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hS
    rw [inv hs]; exact ⟨hs,rfl⟩
  let index (S : Finset ℕ) := ((source S).1:ℝ)
  have data {S} (hS : S ∈ G) := prop _ (member hS).1
  have hG : ∀ S ∈ G, S ⊆ C := fun S h => by
    rw [← (member h).2]; exact (data h).1
  have hE : ∀ S ∈ G, ∑ p ∈ S, e p ≤ δ := fun S h => by
    rw [← (member h).2]; exact (data h).2.2.1
  have hprod {S} (h : S ∈ G) : (∏ p ∈ S,p) = (source S).2 := by
    nth_rw 1 [← (member h).2]; exact (data h).2.1
  have hr := blue_good_recovery hp hx G hG e he hE index (fun S h => by
    dsimp only [index]
    exact_mod_cast hJ _ (mem_sigma.mp (member h).1).1)
    (fun S h => by rw [hprod h]; exact (data h).2.2.2.1)
    (fun S h => by rw [hprod h]; exact (data h).2.2.2.2) k hw sep hu hε
  apply hr.mono
  intro n hn
  apply le_trans _ hn
  apply sub_le_sub_right
  apply le_of_eq
  rw [show G = A.image g from rfl,sum_image inj]
  dsimp only [A]
  rw [sum_sigma]
  apply sum_congr rfl
  intro j hj
  rw [recMass,sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmem : (⟨j,m⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ A := mem_sigma.mpr ⟨hj,hm⟩
  have hi : index (g ⟨j,m⟩) = j := by simp [index,inv hmem]
  rw [hi,hprod (mem_image_of_mem g hmem),inv hmem]

#print axioms blue_bin_recovery
end
end Erdos490Transfer

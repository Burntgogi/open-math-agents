import Cofactor

/-! Finite integer embeddings for distinct dilated prime labels, including an
independent smooth residual and prescribed truncation at the target cutoff. -/
namespace Erdos490Transfer
open Finset
noncomputable section
open Classical

/-- An unused prime goes to blue. Labels outside the target cutoff are
irrelevant, while every prescribed prime inside the window keeps its color. -/
theorem extend_colors (Y m : ℕ) {Q R : Finset ℕ} (hd : Disjoint Q R) :
    ∃ c : Colors Y m, Q ∩ primes Y m ⊆ c.red ∧ R ∩ primes Y m ⊆ c.blue := by
  let A := Q ∩ primes Y m
  have sub : A ⊆ primes Y m := inter_subset_right
  refine ⟨⟨A,primes Y m \ A,union_sdiff_of_subset sub,
    disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)⟩,Subset.rfl,?_⟩
  intro p hp
  exact mem_sdiff.mpr ⟨(mem_inter.mp hp).2,fun ha =>
    disjoint_left.mp hd (mem_inter.mp ha).1 (mem_inter.mp hp).1⟩

/-- Truncating an arbitrary pair of disjoint prescribed supports at m and
completing the prime partition preserves every represented semigroup integer
at every cofactor cutoff m/u. -/
theorem complete_supports {Y m : ℕ} {Q R : Finset ℕ} (hd : Disjoint Q R)
    (hY : ∀ p ∈ Q ∪ R, Nat.Prime p → Y ≤ p) :
    ∃ c : Colors Y m, ∀ u : ℕ, semigroup Q (m/u) ⊆ semigroup c.red (m/u) ∧
      semigroup R (m/u) ⊆ semigroup c.blue (m/u) := by
  obtain ⟨c,hr,hb⟩ := extend_colors Y m hd
  have lift {D E : Finset ℕ} (hD : D ⊆ Q ∪ R) (keep : D ∩ primes Y m ⊆ E) (u : ℕ) :
      semigroup D (m/u) ⊆ semigroup E (m/u) := by
    intro z hz
    obtain ⟨ha,hl⟩ := mem_semigroup.mp hz
    refine mem_semigroup.mpr ⟨Nat.mem_factoredNumbers'.mpr ?_,hl⟩
    intro p hp hdv
    have hm := Nat.mem_factoredNumbers'.mp ha p hp hdv
    exact keep (mem_inter.mpr ⟨hm,mem_filter.mpr ⟨mem_Icc.mpr ⟨hY _ (hD hm) hp,
      (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.1) hdv).trans (hl.trans (Nat.div_le_self ..))⟩,hp⟩⟩)
  exact ⟨c,fun u => ⟨lift subset_union_left hr u,lift subset_union_right hb u⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A choice of 1 omits a label. On retained labels exactly one new prime
from its cell is selected. -/
def ValidLabels (cell : ι → Finset ℕ) (f : ι → ℕ) := ∀ i, f i = 1 ∨ f i ∈ cell i
def high (f : ι → ℕ) := ∏ i, f i
omit [DecidableEq ι] in
lemma high_active {cell : ι → Finset ℕ} {C : Finset ℕ}
    (prime : ∀ i p, p ∈ cell i → Nat.Prime p) (sub : ∀ i, cell i ⊆ C)
    {f : ι → ℕ} (hf : ValidLabels cell f) : Active C (high f) := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hd
  obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  rcases hf i with h|h
  · exact (hp.not_dvd_one (h ▸ hi)).elim
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (prime i _ h)).mp hi
    exact sub i h

omit [DecidableEq ι] in
lemma high_injective {cell : ι → Finset ℕ} (prime : ∀ i p, p ∈ cell i → Nat.Prime p)
    (apart : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) {f g : ι → ℕ}
    (hf : ValidLabels cell f) (hg : ValidLabels cell g) (eq : high f = high g) : f=g := by
  have identify {p} (i : ι) (hp : p ∈ cell i) {v : ι → ℕ} (hv : ValidLabels cell v)
      (hd : p ∣ high v) : p=v i := by
    have hpr := prime i p hp
    obtain ⟨j,_,hj⟩ := (hpr.prime.dvd_finsetProd_iff _).mp hd
    rcases hv j with h|h
    · exact (hpr.not_dvd_one (h ▸ hj)).elim
    · have he := (Nat.prime_dvd_prime_iff_eq hpr (prime j _ h)).mp hj
      have hij : i=j := by
        by_contra hne
        exact disjoint_left.mp (apart i j hne) hp (he ▸ h)
      simpa [hij] using he
  funext i
  rcases hf i with h|h
  · rcases hg i with h'|h'
    · exact h.trans h'.symm
    · exact (identify i h' hf (eq ▸ dvd_prod_of_mem g (mem_univ i))).symm
  · exact identify i h hg (eq ▸ dvd_prod_of_mem f (mem_univ i))

def labelled (F : Finset (ι → ℕ)) (base : Finset ℕ) (n : ℕ) :=
  (F.sigma (fun f => semigroup base (n/high f))).image
    (fun x => high x.1 * x.2)

omit [DecidableEq ι] in
/-- Count disjoint labelled lists after the exact integer cutoff, allowing
every base-semigroup residual, including 1. Any finite collection F can be
used, e.g. the tuples from a chosen family of old squarefree lists. -/
theorem labelled_embedding {cell : ι → Finset ℕ} {C base : Finset ℕ}
    (prime : ∀ i p, p ∈ cell i → Nat.Prime p) (sub : ∀ i, cell i ⊆ C)
    (apart : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) (sep : Disjoint C base)
    (F : Finset (ι → ℕ)) (valid : ∀ f ∈ F, ValidLabels cell f) (n : ℕ) :
    labelled F base n ⊆ semigroup (C ∪ base) n ∧
    (labelled F base n).card = ∑ f ∈ F, (semigroup base (n/high f)).card := by
  constructor
  · intro z hz
    obtain ⟨⟨f,b⟩,hm,rfl⟩ := mem_image.mp hz
    obtain ⟨hf,hb⟩ := mem_sigma.mp hm
    have ha := high_active prime sub (valid _ hf)
    obtain ⟨hb',hl⟩ := mem_semigroup.mp hb
    refine mem_semigroup.mpr ⟨Nat.mul_mem_factoredNumbers
      (Nat.factoredNumbers_mono subset_union_left ha)
      (Nat.factoredNumbers_mono subset_union_right hb'),?_⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha.1)).mp hl
  · rw [labelled,card_image_of_injOn,card_sigma]
    rintro ⟨f,b⟩ hx ⟨g,d⟩ hy he
    obtain ⟨hf,hb⟩ := mem_sigma.mp hx
    obtain ⟨hg,hd⟩ := mem_sigma.mp hy
    have hf' := high_active prime sub (valid _ hf)
    have hg' := high_active prime sub (valid _ hg)
    change high f*b=high g*d at he
    obtain rfl := high_injective prime apart (valid _ hf) (valid _ hg)
      (recover (coprime_active sep hf' (mem_semigroup.mp hd).1)
        (coprime_active sep hg' (mem_semigroup.mp hb).1) he)
    obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf'.1) he
    rfl

/-- Reciprocal mass factors over a Cartesian product of label choices. -/
theorem label_mass (choices : ι → Finset ℕ) :
    (∑ f ∈ Fintype.piFinset choices, ((high f:ℕ):ℝ)⁻¹) =
      ∏ i, ∑ q ∈ choices i, (q:ℝ)⁻¹ := by
  rw [prod_univ_sum]
  simp [high,prod_inv_distrib]

#print axioms labelled_embedding
end
end Erdos490Transfer

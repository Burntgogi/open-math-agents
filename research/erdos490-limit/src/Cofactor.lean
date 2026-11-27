import Mathlib

/-! Exact finite cofactor model for separated pairs in Erdős 490. -/
namespace Erdos490Transfer
open Finset
noncomputable section
open Classical

abbrev Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
def semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (Active C)
def vertices (Y K : ℕ) := semigroup Y.primesBelow K
lemma mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
  simp only [semigroup, mem_filter, mem_Icc]
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩

def Adm (n : ℕ) (A B : Finset ℕ) := A ⊆ Icc 1 n ∧ B ⊆ Icc 1 n ∧
  ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B, a*b=c*d → a=c ∧ b=d
def Sep (Y K : ℕ) (A B : Finset ℕ) :=
  (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
  ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p

def primes (Y n : ℕ) := (Icc Y n).filter Nat.Prime
structure Colors (Y n : ℕ) where
  red : Finset ℕ
  blue : Finset ℕ
  cover : red ∪ blue = primes Y n
  separate : Disjoint red blue

lemma Colors.large {Y n} (c : Colors Y n) : ∀ p ∈ c.red ∪ c.blue, Y ≤ p := by
  rw [c.cover]
  exact fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).1

lemma Colors.small_disjoint {Y n} (c : Colors Y n) :
    Disjoint c.red Y.primesBelow ∧ Disjoint c.blue Y.primesBelow := by
  constructor <;> apply disjoint_left.mpr <;> intro p hp h
  · exact (Nat.mem_primesBelow.mp h).1.not_ge (c.large _ (mem_union_left _ hp))
  · exact (Nat.mem_primesBelow.mp h).1.not_ge (c.large _ (mem_union_right _ hp))

lemma coprime_active {C D : Finset ℕ} {a b : ℕ} (hd : Disjoint C D)
    (ha : Active C a) (hb : Active D b) : a.Coprime b :=
  Nat.coprime_of_dvd fun p hp hx hy => disjoint_left.mp hd
    (Nat.mem_factoredNumbers'.mp ha p hp hx) (Nat.mem_factoredNumbers'.mp hb p hp hy)

lemma recover {a b c d : ℕ} (had : a.Coprime d) (hcb : c.Coprime b)
    (h : a*b=c*d) : a=c :=
  Nat.dvd_antisymm (had.dvd_of_dvd_mul_right (h ▸ dvd_mul_right a b))
    (hcb.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right c d))

/-- Extract the entire small-prime part even when the site's witness contains
some large primes. The small part divides every admissible witness. -/
lemma extract {Y K z w : ℕ} (hz : 0 < z) (hw : w ≤ K) (hd : w ∣ z)
    (hr : ∀ p : ℕ, p.Prime → p ∣ z/w → Y ≤ p) :
    ∃ u ∈ vertices Y K, u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p := by
  let S := z.divisors.filter (Active Y.primesBelow)
  have one : Active Y.primesBelow 1 := by simp [Active,Nat.mem_factoredNumbers]
  obtain ⟨u,hu,hm⟩ := S.exists_max_image id ⟨1,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _,hz.ne'⟩,one⟩⟩
  obtain ⟨hud,hus⟩ := mem_filter.mp hu
  have hdiv := Nat.dvd_of_mem_divisors hud
  have cop : u.Coprime (z/w) := Nat.coprime_of_dvd fun p hp hpu hpz =>
    (Nat.mem_primesBelow.mp (Nat.mem_factoredNumbers'.mp hus p hp hpu)).1.not_ge (hr p hp hpz)
  have huw := cop.dvd_of_dvd_mul_right (show u ∣ w*(z/w) by rwa [Nat.mul_div_cancel' hd])
  refine ⟨u,mem_semigroup.mpr ⟨hus,(Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd hz) huw).trans hw⟩,hdiv,?_⟩
  intro p hp hpu
  by_contra! hh
  have hps : Active Y.primesBelow p := by
    apply Nat.mem_factoredNumbers'.mpr
    intro q hq hqp
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact Nat.mem_primesBelow.mpr ⟨hh,hq⟩
  have hmax := hm (u*p) (mem_filter.mpr ⟨Nat.mem_divisors.mpr
    ⟨(Nat.dvd_div_iff_mul_dvd hdiv).mp hpu,hz.ne'⟩,Nat.mul_mem_factoredNumbers hus hps⟩)
  have hlt := Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.pos_of_ne_zero hus.1)
  simp only [id_eq] at hmax
  omega

def Covers (Y K n : ℕ) (C A : Finset ℕ) := ∀ z ∈ A,
  ∃ h ∈ semigroup C n, ∃ u ∈ vertices Y K, h*u=z

theorem colors_cover {Y K n A B} (ha : Adm n A B) (hs : Sep Y K A B) :
    ∃ c : Colors Y n, Covers Y K n c.red A ∧ Covers Y K n c.blue B := by
  let Q := (primes Y n).filter (fun p => ∃ a ∈ A, p ∣ a)
  let R := primes Y n \ Q
  let c : Colors Y n := ⟨Q,R,by ext; simp [Q,R]; tauto, disjoint_left.mpr (fun {_} h h' => (mem_sdiff.mp h').2 h)⟩
  have split {C T : Finset ℕ} (ht : T ⊆ A ∪ B) (bound : T ⊆ Icc 1 n)
      (color : ∀ z ∈ T, ∀ p ∈ primes Y n, p ∣ z → p ∈ C) : Covers Y K n C T := by
    intro z hz
    obtain ⟨hz0,hzn⟩ := mem_Icc.mp (bound hz)
    obtain ⟨w,hw,hd,hr⟩ := hs.2 z (ht hz)
    obtain ⟨u,hu,hd,hr⟩ := extract hz0 hw hd hr
    refine ⟨z/u,mem_semigroup.mpr ⟨Nat.mem_factoredNumbers'.mpr ?_,(Nat.div_le_self ..).trans hzn⟩,u,hu,Nat.div_mul_cancel hd⟩
    intro p hp hpd
    have hdv := hpd.trans (Nat.div_dvd_of_dvd hd)
    exact color z hz p (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr p hp hpd,(Nat.le_of_dvd hz0 hdv).trans hzn⟩,hp⟩) hdv
  refine ⟨c,split subset_union_left ha.1 (fun z hz p hp hd => mem_filter.mpr ⟨hp,z,hz,hd⟩),
    split subset_union_right ha.2.1 ?_⟩
  intro b hb p hp hd
  refine mem_sdiff.mpr ⟨hp,?_⟩
  intro h
  obtain ⟨a,ha',hd'⟩ := (mem_filter.mp h).2
  exact hs.1 a ha' b hb p (mem_filter.mp hp).2 (mem_Icc.mp (mem_filter.mp hp).1).1 hd' hd

/-- A graph is specified by the increasing quotients of its edges. -/
def ratios (S : Finset ℕ) : Finset ℚ :=
  ((S ×ˢ S).filter (fun t => t.1 < t.2)).image (fun t => (t.2 : ℚ)/t.1)
lemma mem_ratios {S q} : q ∈ ratios S ↔ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (b:ℚ)/a=q := by
  simp only [ratios,mem_image,mem_filter,mem_product, Prod.exists]
  constructor
  · rintro ⟨a,b,⟨⟨ha,hb⟩,hlt⟩,he⟩
    exact ⟨a,ha,b,hb,hlt,he⟩
  · rintro ⟨a,ha,b,hb,hlt,he⟩
    exact ⟨a,b,⟨⟨ha,hb⟩,hlt⟩,he⟩

lemma ratios_mono {S T : Finset ℕ} (h : S ⊆ T) : ratios S ⊆ ratios T := by
  intro q hq
  obtain ⟨a,ha,b,hb,hl,he⟩ := mem_ratios.mp hq
  exact mem_ratios.mpr ⟨a,h ha,b,h hb,hl,he⟩

def fiber (U A : Finset ℕ) (h : ℕ) := U.filter (fun u => h*u ∈ A)
def oldGraph (U H A : Finset ℕ) := H.biUnion (fun h => ratios (fiber U A h))

lemma oldGraph_subset (U H A) : oldGraph U H A ⊆ ratios U := by
  intro q hq
  obtain ⟨h,_,hm⟩ := mem_biUnion.mp hq
  exact ratios_mono (filter_subset ..) hm

lemma ratio_eq {a b c d : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) :
    (b:ℚ)/a=(d:ℚ)/c ↔ b*c=d*a := by
  rw [div_eq_div_iff (by exact_mod_cast ha) (by exact_mod_cast hc)]
  exact_mod_cast Iff.rfl

lemma old_blue {Y K n A B} (ha : Adm n A B) (c : Colors Y n)
    {h} (_hh : h ∈ semigroup c.blue n) : Disjoint
      (ratios (fiber (vertices Y K) B h)) (oldGraph (vertices Y K) (semigroup c.red n) A) := by
  apply disjoint_left.mpr
  intro q hq hg
  obtain ⟨k,hk,hg⟩ := mem_biUnion.mp hg
  obtain ⟨a,ha',b,hb',hlt,he⟩ := mem_ratios.mp hg
  obtain ⟨d,hd,e,he',_,hf⟩ := mem_ratios.mp hq
  have ha0 := (mem_semigroup.mp (mem_filter.mp ha').1).1.1
  have hd0 := (mem_semigroup.mp (mem_filter.mp hd).1).1.1
  have eq := (ratio_eq ha0 hd0).mp (he.trans hf.symm)
  have coll := ha.2.2 _ (mem_filter.mp hb').2 _ (mem_filter.mp hd).2 _
    (mem_filter.mp ha').2 _ (mem_filter.mp he').2 (by nlinarith only [congrArg (fun v => (k*h)*v) eq])
  exact hlt.ne (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mem_semigroup.mp hk).1.1) coll.1.symm)

end
end Erdos490Transfer

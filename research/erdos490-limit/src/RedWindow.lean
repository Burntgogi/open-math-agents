import RedSampling
import RedArithmetic
import OldSupport

open Real Filter Finset MeasureTheory Set
open scoped Topology
namespace Erdos490PrimeCells

noncomputable def harmonicSize (i : Label) := log (i.hi/i.lo)

theorem harmonicSize_pos (i : Label) : 0 < harmonicSize i :=
  log_pos ((one_lt_div i.positive).mpr i.nonempty)

theorem red_window_recovery {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (y : ι → ℝ) (i : ι → Label) (n : ι → ℕ) (L : (s : ι) → Fin (n s) → Label)
    {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z-B) z)
    (hsupport : ∀ s ∈ S, ∀ᵐ v ∂(labelSum limitFactor (i s :: List.ofFn (L s)) : Measure ℝ),
      v ∈ Icc (y s-δ) (y s+δ)) {E : Set ℝ} (hE : E.Finite) :
    let W := fun s => harmonicSize (i s) * ∏ j,harmonicSize (L s j)
    ∃ x ∈ Icc (z-B-δ) (z+δ), x ∉ E ∧ ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      exp (-2*δ)*(∑ s ∈ S,W s * exp (y s-z)) - ε ≤
        t*exp (-(t*x-c))*(∑ s ∈ S,finalCount (i s) (L s) t x c) := by
  classical
  let W (s : ι) := harmonicSize (i s) * ∏ j,harmonicSize (L s j)
  have hw (s : ι) : 0 < W s := mul_pos (harmonicSize_pos _) (Finset.prod_pos fun j _ => harmonicSize_pos _)
  have H := exists_redSampling_labelDensity_ge S y W i (fun s => List.ofFn (L s)) hB hδ hy
    (fun s _ => (hw s).le) hsupport (Finset.sum_pos (fun s _ => mul_pos (hw s) (exp_pos _)) hS).ne' hE
  obtain ⟨x,hx,hreg,hx'⟩ := H
  refine ⟨x,hx,hreg,fun c ε hε => ?_⟩
  let η := ε/(S.card+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsum := (Finset.eventually_all (I := S)).mpr (fun s _ => final_count_lower (i s) (L s) x c hη)
  filter_upwards [hsum] with t ht
  let d (s : ι) := labelDensity (i s) (List.ofFn (L s)) x
  have eq (s : ι) : W s * (d s / log ((i s).hi/(i s).lo)) = (∏ j,harmonicSize (L s j)) * d s := by
    change (harmonicSize (i s) * _) * (d s / harmonicSize (i s)) = _
    field_simp [(harmonicSize_pos (i s)).ne']
  simp only [← show ∀ s,d s=labelDensity (i s) (List.ofFn (L s)) x from fun _ => rfl] at hx'
  simp_rw [eq] at hx'
  nth_rw 2 [Finset.mul_sum]
  have h₁ := Finset.sum_le_sum (fun s hs => ht s hs)
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at h₁
  have hc : (S.card:ℝ)*η ≤ ε := by
    calc
      _ ≤ (S.card+1)*η := by gcongr; linarith
      _ = ε := by dsimp [η]; field_simp
  exact (sub_le_sub hx' hc).trans h₁

#print axioms red_window_recovery
end Erdos490PrimeCells

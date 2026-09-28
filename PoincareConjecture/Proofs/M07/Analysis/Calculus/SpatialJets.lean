import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

set_option autoImplicit false

open scoped ContDiff Topology Pointwise
open Set

namespace Poincare.Analysis

theorem iteratedFDeriv_spatial_slice
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × E → F) {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (t, x)) (r : ℕ)
    (v : Fin r → E) :
    iteratedFDeriv ℝ r (fun y => f (t, y)) x v =
      iteratedFDeriv ℝ r f (t, x) (fun i => (0, v i)) := by
  let a : ℝ × E := (t, 0)
  let ι : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have hr_le : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change (↑(r : ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hr_ne : (r : ℕ∞ω) ≠ (∞ : ℕ∞ω) := by
    change (↑(r : ℕ∞) : ℕ∞ω) ≠ (↑(⊤ : ℕ∞) : ℕ∞ω)
    intro h
    have h' : (r : ℕ∞) = (⊤ : ℕ∞) := WithTop.coe_inj.mp h
    exact WithTop.coe_ne_top h'
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (r : ℕ∞ω)) hr_le (by
    intro hr
    exact (hr_ne hr).elim)
  obtain ⟨s, hsu, hsopen, hxs⟩ := mem_nhds_iff.mp hu
  let s' : Set (ℝ × E) := (fun z : ℝ × E => a + z) ⁻¹' s
  have hs'open : IsOpen s' := hsopen.preimage (continuous_const.add continuous_id)
  have hshift : ContDiffOn ℝ (r : ℕ∞ω) (fun z : ℝ × E => f (a + z)) s' := by
    apply hfu.comp
    · exact (contDiff_const.add contDiff_id).contDiffOn
    · intro z hz
      change a + z ∈ s at hz
      exact hsu hz
  have hιopen : IsOpen (ι ⁻¹' s') := hs'open.preimage ι.continuous
  have hιx : ι x ∈ s' := by
    change a + (0, x) ∈ s
    simpa [a] using hxs
  have hcomp := ι.iteratedFDerivWithin_comp_right hshift hs'open.uniqueDiffOn
    hιopen.uniqueDiffOn hιx (i := r) (by simp)
  have hset : a +ᵥ s' = s := by
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [s']
  have hleft := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := (fun z : E => f (a + ι z))) (s := ι ⁻¹' s') r hιopen hιx
  have hright := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := f)
    (s := s') r a (ι x)
  calc
    iteratedFDeriv ℝ r (fun y => f (t, y)) x v =
        iteratedFDerivWithin ℝ r ((fun z : ℝ × E => f (a + z)) ∘ ι)
          (ι ⁻¹' s') x v := by
      change iteratedFDeriv ℝ r (fun y => f (t, y)) x v =
        (iteratedFDerivWithin ℝ r (fun z : E => f (a + ι z))
          (ι ⁻¹' s') x) v
      rw [hleft]
      simp [a, ι]
    _ = ((iteratedFDerivWithin ℝ r (fun z : ℝ × E => f (a + z))
          s' (ι x)).compContinuousLinearMap (fun _ => ι)) v := by
      rw [hcomp]
    _ = iteratedFDeriv ℝ r f (t, x) (fun i => (0, v i)) := by
      rw [hright, hset]
      have hax : a + ι x = (t, x) := by simp [a, ι]
      rw [hax]
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r hsopen hxs]
      simp [ι]

end Poincare.Analysis

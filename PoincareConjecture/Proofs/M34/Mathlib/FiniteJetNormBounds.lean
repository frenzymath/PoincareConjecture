import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

open scoped ContDiff BigOperators

namespace Poincare.Analysis.Calculus

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_iteratedFDeriv_directional_le {f : E → F} {x : E} (m : ℕ)
    (hf : ContDiffAt 𝕜 (m + 1) f x) (v : E) :
    ‖iteratedFDeriv 𝕜 m (fun y => fderiv 𝕜 f y v) x‖ ≤
      ‖ContinuousLinearMap.apply 𝕜 F v‖ * ‖iteratedFDeriv 𝕜 (m + 1) f x‖ := by
  simpa only [norm_iteratedFDeriv_fderiv, Function.comp_def,
    ContinuousLinearMap.apply_apply] using
    (ContinuousLinearMap.apply 𝕜 F v).norm_iteratedFDeriv_comp_left
      (hf.fderiv_right (m := (m : ℕ∞ω)) (by simp)) (le_refl _)

theorem norm_iteratedFDeriv_sub_le_of_contDiffAt {f g : E → F} {x : E} (m : ℕ)
    (hf : ContDiffAt 𝕜 m f x) (hg : ContDiffAt 𝕜 m g x) :
    ‖iteratedFDeriv 𝕜 m (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv 𝕜 m f x‖ + ‖iteratedFDeriv 𝕜 m g x‖ := by
  change ‖iteratedFDeriv 𝕜 m (f - g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply hf hg]
  exact norm_sub_le _ _

theorem norm_iteratedFDeriv_sum_le_of_contDiffAt {ι : Type*} (s : Finset ι)
    {f : ι → E → F} {x : E} (m : ℕ)
    (hf : ∀ i ∈ s, ContDiffAt 𝕜 m (f i) x) :
    ‖iteratedFDeriv 𝕜 m (fun y => ∑ i ∈ s, f i y) x‖ ≤
      ∑ i ∈ s, ‖iteratedFDeriv 𝕜 m (f i) x‖ := by
  have hfun : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun, iteratedFDeriv_sum_apply hf]
  exact norm_sum_le _ _

end Poincare.Analysis.Calculus

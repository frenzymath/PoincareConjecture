import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod












set_option autoImplicit false

open Set
open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]



theorem ContinuousAffineMap.iteratedFDerivWithin_comp_right
    (g : G →ᴬ[𝕜] E) {f : E → F} {s : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hpre : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G} (hx : g x ∈ s)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap
        (fun _ => g.contLinear) :=
  (((hf.of_le hi).ftaylorSeriesWithin hs).comp_continuousAffineMap g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hpre hx).symm




theorem iteratedFDeriv_prod_slice_eq_within
    {f : G × E → F} {J : Set G} {U : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 n f (J ×ˢ U)) (hJ : UniqueDiffOn 𝕜 J) (hU : IsOpen U)
    {t : G} (ht : t ∈ J) {x : E} (hx : x ∈ U) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun y => f (t, y)) x =
      (iteratedFDerivWithin 𝕜 i f (J ×ˢ U) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr 𝕜 G E) := by
  let g : E →ᴬ[𝕜] G × E :=
    (ContinuousAffineMap.const 𝕜 E t).prod (ContinuousAffineMap.id 𝕜 E)
  have hpre : g ⁻¹' (J ×ˢ U) = U := by
    ext y
    simp [g, ht]
  have hlinear : g.contLinear = ContinuousLinearMap.inr 𝕜 G E := by
    ext v <;> rfl
  have hpre_diff : UniqueDiffOn 𝕜 (g ⁻¹' (J ×ˢ U)) := by
    rw [hpre]
    exact hU.uniqueDiffOn
  have h := g.iteratedFDerivWithin_comp_right hf (hJ.prod hU.uniqueDiffOn)
    hpre_diff (show g x ∈ J ×ˢ U from ⟨ht, hx⟩) hi
  rw [hpre, iteratedFDerivWithin_of_isOpen i hU hx, hlinear] at h
  exact h

import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.FiniteBilinearCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth finite bilinear reconstruction and parameter pullback

These local calculus facts retain the fixed model norms. They supply
the smooth germs needed in the finite-jet pullback estimate in the
Morgan-Tian Theorem 12.28 argument, pp. 323-324.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open scoped ContDiff

/-- Finite smooth coefficient germs reconstruct a smooth bilinear germ. -/
theorem ContDiffAt.piLpBilinearFromCoordinates
    {𝕜 E F I J : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [Fintype I] [Fintype J]
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {n : ℕ∞ω} {f : E → I → J → F} {x : E}
    (hf : ∀ i j, ContDiffAt 𝕜 n (fun y => f y i j) x) :
    ContDiffAt 𝕜 n (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := p) (q := q) (𝕜 := 𝕜) (f y)) x := by
  let L : (I → J → F) →L[𝕜]
      (PiLp p fun _ : I => 𝕜) →L[𝕜] (PiLp q fun _ : J => 𝕜) →L[𝕜] F :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  exact L.contDiff.contDiffAt.comp x (contDiffAt_pi.2 (fun i => contDiffAt_pi.2 (hf i)))

/-- A smooth bilinear coefficient field and a smooth parameter map
have a smooth bilinear pullback on a neighborhood of the base point. -/
theorem ContDiffAt.bilinearPullback
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hB : ContDiffAt ℝ ∞ B (f x)) :
    ContDiffAt ℝ ∞ (fun y => (B (f y)).bilinearComp
      (fderiv ℝ f y) (fderiv ℝ f y)) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have h₁ := ((hB.comp x hf).clm_comp hd)
  let A := (ContinuousLinearMap.flipₗᵢ ℝ E F G).toContinuousLinearEquiv.toContinuousLinearMap
  let D := (ContinuousLinearMap.flipₗᵢ ℝ E E G).toContinuousLinearEquiv.toContinuousLinearMap
  have h₂ := A.contDiff.contDiffAt.comp x h₁
  have h₃ := h₂.clm_comp hd
  exact D.contDiff.contDiffAt.comp x h₃

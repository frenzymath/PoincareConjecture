import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.BilinearForm










set_option autoImplicit false

namespace ContinuousLinearMap




theorem IsInvertible.det_bilinear_basis_ne_zero
    {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    {A : E →L[𝕜] E →L[𝕜] 𝕜} (hA : A.IsInvertible) (b : Module.Basis ι 𝕜 E) :
    (Matrix.of (fun i j => A (b i) (b j))).det ≠ 0 := by
  let : FiniteDimensional 𝕜 E := Module.Finite.of_basis b
  have hsep : A.toBilinForm.SeparatingLeft := by
    intro x hx
    apply hA.injective
    rw [map_zero]
    ext y
    exact hx y
  have hnd := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  convert! h using 1
  congr 1
  ext i j
  simp only [Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply,
    ContinuousLinearMap.toBilinForm_apply]

end ContinuousLinearMap

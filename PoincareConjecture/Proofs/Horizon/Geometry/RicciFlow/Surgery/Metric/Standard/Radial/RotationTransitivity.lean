import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.AxisCoefficients
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace PoincareConjecture.MetricSurgery

noncomputable def rotationOfIsometry (L : StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace)
    (hdet : LinearMap.det L.toLinearMap = 1) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨L.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨
      L.toMatrix_mem_unitaryGroup _ _, by
        rw [LinearMap.det_toMatrix]
        exact hdet⟩⟩

theorem rotationOfIsometry_apply (L : StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace)
    (hdet : LinearMap.det L.toLinearMap = 1) (v : StandardCapSpace) :
    standardRotation (rotationOfIsometry L hdet) v = L v := by
  rw [standardRotation_eq_linear, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  change Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap) v = L v
  rw [Matrix.toLin_toMatrix]
  rfl

theorem exists_axis_isometry (u : StandardCapSpace) (hu : ‖u‖ = 1) :
    ∃ L : StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace,
      LinearMap.det L.toLinearMap = 1 ∧ L (axisBasis 0) = u := by
  by_cases heq : axisBasis 0 = u
  · refine ⟨LinearIsometryEquiv.refl ℝ StandardCapSpace, ?_, heq⟩
    simp
  let D := (ℝ ∙ axisBasis 1)ᗮ.reflection
  let H := (ℝ ∙ (axisBasis 0 - u))ᗮ.reflection
  have hD : D (axisBasis 0) = axisBasis 0 := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [axisBasis, EuclideanSpace.inner_single_left]
  have hH : H (axisBasis 0) = u := by
    apply Submodule.reflection_sub
    simpa [axisBasis] using hu.symm
  have hDdet : LinearMap.det D.toLinearMap = -1 := by
    dsimp [D]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton (axisBasis_ne_zero 1)]
    norm_num
  have hHdet : LinearMap.det H.toLinearMap = -1 := by
    dsimp [H]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton (sub_ne_zero.mpr heq)]
    norm_num
  refine ⟨D.trans H, ?_, ?_⟩
  · change LinearMap.det (H.toLinearMap.comp D.toLinearMap) = 1
    rw [LinearMap.det_comp, hHdet, hDdet]
    norm_num
  · change H (D (axisBasis 0)) = u
    rw [hD, hH]

theorem standardInitialMetric_isometry_inner (g₀ : StandardInitialMetric)
    (L : StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace)
    (hdet : LinearMap.det L.toLinearMap = 1) (x v w : StandardCapSpace) :
    g₀.metric.inner (L x) (L v) (L w) = g₀.metric.inner x v w := by
  have h := standardInitialMetric_rotation_inner g₀ (rotationOfIsometry L hdet) x v w
  change g₀.metric.inner (standardRotation (rotationOfIsometry L hdet) x)
    (standardRotation (rotationOfIsometry L hdet) v)
    (standardRotation (rotationOfIsometry L hdet) w) = _ at h
  let G : StandardCapSpace → StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner
  change G (standardRotation (rotationOfIsometry L hdet) x)
    (standardRotation (rotationOfIsometry L hdet) v)
    (standardRotation (rotationOfIsometry L hdet) w) = G x v w at h
  simp only [rotationOfIsometry_apply] at h
  exact h

end PoincareConjecture.MetricSurgery

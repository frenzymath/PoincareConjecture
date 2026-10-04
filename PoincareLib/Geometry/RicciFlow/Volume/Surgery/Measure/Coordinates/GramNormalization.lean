import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.PullbackJacobian

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/GramNormalization.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Constant source normalization of the actual Gram Jacobian

Freezing the source vectors whose endpoint images are orthonormal changes the
Jacobian by the norm determinant of one fixed linear map. This factor is
retained explicitly when differentiating at the chosen time.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback Gram determinant under a fixed linear source change. -/
theorem sqrt_det_pullbackMetric_change_source (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (C : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (Matrix.det (fun i j : Fin n ↦ pullbackMetricForm g f x
      (C (EuclideanSpace.basisFun (Fin n) ℝ i))
      (C (EuclideanSpace.basisFun (Fin n) ℝ j)))) =
        pullbackJacobian g f x * C.normDet := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  have hs := (D.comp C).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [RCLike.ofReal_real_eq_id, id_eq] at hs
  change Real.sqrt (Matrix.gram ℝ (fun i ↦ (D.comp C)
      (EuclideanSpace.basisFun (Fin n) ℝ i))).det = _
  rw [← hs, Real.sqrt_sq (D.comp C).normDet_nonneg,
    LinearMap.normDet_comp_of_finrank_eq C D rfl,
    pullbackJacobian_eq_normDet]

/-- An invertible constant source change has a strictly positive normalization factor. -/
theorem source_normalization_normDet_pos
    (C : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    0 < C.toLinearMap.normDet := by
  refine lt_of_le_of_ne C.toLinearMap.normDet_nonneg ?_
  exact Ne.symm (fun h ↦ LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h
    (LinearMap.ker_eq_bot.mpr C.injective))

end PoincareMT.SurgeryVolume.Measure

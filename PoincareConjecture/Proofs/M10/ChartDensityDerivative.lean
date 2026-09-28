import PoincareConjecture.Proofs.M10.ChartDensitySmooth
import PoincareConjecture.Proofs.M10.GramNormalization
import PoincareConjecture.Proofs.M10.JacobianEvolution
import PoincareConjecture.Proofs.M10.MetricTrace









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in


theorem pullbackJacobian_fderiv_eq (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {y : EuclideanSpace ℝ (Fin n)}
    (hB : ContDiffAt ℝ 1 (pullbackMetricForm g f) y)
    (hD : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f y))
    (C : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hC : ∀ v, mfderiv (𝓡 n) (𝓡 n) f y (C v) = metricCoordinates g (f y) v)
    (w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (pullbackJacobian g f) y w = pullbackJacobian g f y *
      ((∑ i : Fin n, fderiv ℝ (pullbackMetricForm g f) y w
        (C (EuclideanSpace.basisFun (Fin n) ℝ i))
        (C (EuclideanSpace.basisFun (Fin n) ℝ i))) / 2) := by
  let β := fun i : Fin n ↦ C (EuclideanSpace.basisFun (Fin n) ℝ i)
  let A := fun s : ℝ ↦
    (fun i j : Fin n ↦ pullbackMetricForm g f (y + s • w) (β i) (β j))
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    fderiv ℝ (pullbackMetricForm g f) y w (β i) (β j)
  let J := fun s : ℝ ↦ pullbackJacobian g f (y + s • w)
  have hline : HasDerivAt (fun s : ℝ ↦ y + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hBD := (hB.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have hA : HasDerivAt A Q 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [Function.comp_def, map_zero, add_zero, zero_add] using
      (hBD.clm_apply (hasDerivAt_const 0 (β i))).clm_apply (hasDerivAt_const 0 (β j))
  have hAt : A 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    dsimp only [A]
    rw [zero_smul, add_zero]
    change g.inner (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
      (mfderiv (𝓡 n) (𝓡 n) f y (C (EuclideanSpace.basisFun (Fin n) ℝ j))) = _
    rw [hC, hC, metricCoordinates_basis_inner, Matrix.one_apply]
  have hscale : (fun s ↦ C.toLinearMap.normDet * J s) =ᶠ[𝓝 0]
      (fun s ↦ Real.sqrt (Matrix.det (A s))) := by
    apply Eventually.of_forall
    intro s
    convert (sqrt_det_pullbackMetric_change_source g f (y + s • w) C.toLinearMap).symm using 1
    · exact mul_comm _ _
    · rfl
  have hJ := hasDerivAt_jacobian_of_scaled_normalized_gram
    (source_normalization_normDet_pos C).ne' hscale hA hAt
  have hactual := ((pullbackJacobian_contDiffAt_of_form g hB hD).differentiableAt
    one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heq := hactual.unique hJ
  simpa only [J, zero_smul, add_zero, Matrix.trace, Matrix.diag, Q, β] using heq

end PoincareConjecture.M10

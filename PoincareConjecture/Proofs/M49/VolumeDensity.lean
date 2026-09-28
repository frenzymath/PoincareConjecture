import PoincareConjecture.Proofs.M10.GramNormalization
import PoincareConjecture.Proofs.M10.MetricTrace
import PoincareConjecture.Proofs.M10.JacobianEvolution











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)



theorem pullbackJacobian_continuousOn_time
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun t => M10.pullbackJacobian (F.metric t) f x) J := by
  intro t ht
  have hmatrix : ContinuousWithinAt (fun s => (fun i j : Fin n =>
      M10.pullbackMetricForm (F.metric s) f x
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j))) J t :=
    continuousWithinAt_pi.mpr fun i => continuousWithinAt_pi.mpr fun j =>
      (F.equation t ht (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) f x
          (EuclideanSpace.basisFun (Fin n) ℝ j))).continuousWithinAt
  exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
    (continuous_id.matrix_det.continuousAt.comp_continuousWithinAt hmatrix)

set_option backward.isDefEq.respectTransparency false in


theorem pullbackJacobian_hasDerivAt
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hD : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {t : ℝ} (ht : J ∈ 𝓝 t) :
    HasDerivAt (fun s => M10.pullbackJacobian (F.metric s) f x)
      (-(F.connection t).scalarCurvature (f x) *
        M10.pullbackJacobian (F.metric t) f x) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap hD)
  let C := (M10.metricCoordinates (F.metric t) (f x)).toContinuousLinearEquiv.trans
    D.symm
  have hC (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) f x (C v) = M10.metricCoordinates (F.metric t) (f x) v := by
    change D (C v) = _
    simp only [C, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  let A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s => fun i j =>
    M10.pullbackMetricForm (F.metric s) f x
      (C (EuclideanSpace.basisFun (Fin n) ℝ i))
      (C (EuclideanSpace.basisFun (Fin n) ℝ j))
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    -2 * (F.connection t).ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ j)))
  have hA : HasDerivAt A B t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j =>
      (F.equation t (mem_of_mem_nhds ht) (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
        (mfderiv (𝓡 n) (𝓡 n) f x
          (C (EuclideanSpace.basisFun (Fin n) ℝ j)))).hasDerivAt ht
  have hAt : A t = 1 := by
    ext i j
    change (F.metric t).inner (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ j))) = _
    rw [hC, hC, M10.metricCoordinates_basis_inner, Matrix.one_apply]
  have hscale :
      (fun s => C.toLinearMap.normDet * M10.pullbackJacobian (F.metric s) f x) =ᶠ[𝓝 t]
        (fun s => Real.sqrt (A s).det) := by
    apply Eventually.of_forall
    intro s
    simpa only [A, mul_comm] using!
      (M10.sqrt_det_pullbackMetric_change_source (F.metric s) f x C.toLinearMap).symm
  have htrace : B.trace / 2 = -(F.connection t).scalarCurvature (f x) := by
    change (∑ i : Fin n, -2 * (F.connection t).ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
      (mfderiv (𝓡 n) (𝓡 n) f x (C (EuclideanSpace.basisFun (Fin n) ℝ i)))) / 2 = _
    simp_rw [hC]
    rw [← Finset.mul_sum, M10.sum_metricCoordinates_ricci]
    ring
  have h := M10.hasDerivAt_jacobian_of_scaled_normalized_gram
    (M10.source_normalization_normDet_pos C).ne' hscale hA hAt
  rw [htrace] at h
  simpa only [mul_comm] using h

end PoincareConjecture.M49

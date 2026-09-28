import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.CovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedSpatialContact







noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}


def metricDifferenceTensor
    (g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
  fun x v => h.inner x (v 0) (v 1) - g.inner x (v 0) (v 1)

theorem metricDifferenceTensor_isSmooth
    (g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    IsSmoothCovariantTensor (metricDifferenceTensor g h) :=
  (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor h).sub
    (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g)



theorem tendsto_scalarCurvature_of_covariant_metric_jets
    {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g)
    {h : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D' : ∀ i, LeviCivitaData (h i)) (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 2 → Tendsto (fun i => g.tensorNorm
      (D.iteratedCovariantTensorDerivative (metricDifferenceTensor g (h i)) r) x)
      l (𝓝 0)) :
    Tendsto (fun i => (D' i).scalarCurvature x) l (𝓝 (D.scalarCurvature x)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  apply LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets D' D x b
  intro r hr a c
  have he := tendsto_iteratedFDeriv_tensor_apply_zero D
    (fun i => metricDifferenceTensor_isSmooth g (h i)) x hjets r hr ![b a, b c]
  have hsm (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      ContDiffAt ℝ r (fun y => g'.inner y (b a) (b c)) x := by
    have hs : ContDiffAt ℝ ∞ (fun y => g'.inner y (b a) (b c)) x :=
      ((g'.contDiffAt_euclideanCoefficients x).clm_apply
        contDiffAt_const).clm_apply contDiffAt_const
    exact hs.of_le (by norm_cast; exact le_top)
  have hid (i : ι) :
      iteratedFDeriv ℝ r (fun y => metricDifferenceTensor g (h i) y ![b a, b c]) x =
        iteratedFDeriv ℝ r (fun y => (h i).inner y (b a) (b c)) x -
          iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x := by
    simpa only [metricDifferenceTensor, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one] using fun_iteratedFDeriv_sub_apply (hsm (h i)) (hsm g)
  simp_rw [hid] at he
  simpa only [sub_add_cancel, zero_add] using he.add_const
    (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)



theorem exists_scalar_control_of_covariant_metric_twoJet
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n))
    {α : ℝ} (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData h),
      (∀ r : ℕ, r ≤ 2 →
        g.tensorNorm (D.iteratedCovariantTensorDerivative (metricDifferenceTensor g h) r) x < δ) →
      |D'.scalarCurvature x - D.scalarCurvature x| < α := by
  let Data := (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) × LeviCivitaData h
  let J : Data → Fin 3 → ℝ := fun p r => g.tensorNorm
    (D.iteratedCovariantTensorDerivative (metricDifferenceTensor g p.1) r.val) x
  let L := Filter.comap J (𝓝 0)
  have hJ : Tendsto J L (𝓝 0) := tendsto_comap
  have hjets (r : ℕ) (hr : r ≤ 2) : Tendsto (fun p : Data => g.tensorNorm
      (D.iteratedCovariantTensorDerivative (metricDifferenceTensor g p.1) r) x) L (𝓝 0) := by
    exact ((continuous_apply (⟨r, by omega⟩ : Fin 3)).tendsto 0).comp hJ
  have hscalar := tendsto_scalarCurvature_of_covariant_metric_jets D
    (fun p : Data => p.2) x hjets
  obtain ⟨δ, hδ, hbound⟩ := (Metric.nhds_basis_ball.comap J).mem_iff.mp
    (hscalar (Metric.ball_mem_nhds (D.scalarCurvature x) hα))
  refine ⟨δ, hδ, fun h D' hclose => ?_⟩
  have hJclose : J ⟨h, D'⟩ ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro r
    simpa only [Real.dist_eq, Pi.zero_apply, sub_zero,
      J, RiemannianMetric.tensorNorm, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hclose r.val (by omega)
  simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hbound hJclose

end PoincareConjecture.SingularRegularLimit.RoundComparison

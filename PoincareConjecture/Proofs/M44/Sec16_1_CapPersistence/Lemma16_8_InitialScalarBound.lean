import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_IntrinsicScalarBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialCurvatureBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_LocalScalarTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

noncomputable local instance initialScalarCoefficientNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialScalarCoefficientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace




theorem scalar_bound_of_normalized_comparison
    {g0 : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta K : ℝ}
    (Q : SurgeryCapClose g0 S g tip scale eta) (hsmall : eta ≤ 1 / 4)
    (hK : 0 ≤ K) (hcurv : ∀ x, g0.connection.curvatureTensorNorm x ≤ K)
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] (h : RiemannianMetric 3 N) (D : LeviCivitaData h)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (hsub : a.source ⊆ g0.metric.ball 0 eta⁻¹)
    (hlink : EqOn (h.pullbackCoefficients a) Q.normalizedCoefficients a.source)
    {x : E} (hx : x ∈ a.source) :
    |D.scalarCurvature (a x)| ≤ 72 * (K + 3) := by
  have horder : 2 ≤ ⌊eta⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ Q.eta_pos]
    linarith
  have hinv (y : E) (hy : y ∈ a.source) :
      (mfderiv (𝓡 3) (𝓡 3) a y).IsInvertible :=
    ⟨(a.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  obtain ⟨gE, DE, V, hV, hxV, hVa, hmetric⟩ :=
    RiemannianMetric.exists_local_realization a.open_source hx (h.pullbackCoefficients a)
      (fun y hy => (h.contDiffAt_pullbackCoefficients
        (a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds hy))).contDiffWithinAt)
      (fun y _ v w => h.symm (a y) _ _)
      (fun y hy v hv => by
        apply h.pos (a y)
        intro hz
        apply hv
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have hcoeff : gE.euclideanCoefficients =ᶠ[𝓝 x] Q.normalizedCoefficients :=
    eventually_of_mem (hV.mem_nhds hxV)
      (fun y hy => (hmetric y hy).trans (hlink (hVa hy)))
  have herr : metricError g0.metric gE =ᶠ[𝓝 x]
      (fun (y : E) (v : Fin 2 → E) =>
        scale⁻¹ ^ 2 * surgeryCapPullback g Q.map y v - g0.metric.inner y (v 0) (v 1)) := by
    filter_upwards [hcoeff] with y hy
    funext v
    change gE.euclideanCoefficients y (v 0) (v 1) - _ = _
    rw [hy]
    rfl
  have herror (j : ℕ) (hj : j ≤ 2) :
      g0.metric.tensorNorm (g0.connection.iteratedCovariantTensorDerivative
        (metricError g0.metric gE) j) x ≤ eta := by
    have heq := (M36.comparison_iteratedCovariantTensorDerivative_eventuallyEq
      g0.connection herr j).self_of_nhds
    have hn : g0.metric.tensorNorm (g0.connection.iteratedCovariantTensorDerivative
        (metricError g0.metric gE) j) x =
        g0.metric.tensorNorm (g0.connection.iteratedCovariantTensorDerivative
          (fun y v => scale⁻¹ ^ 2 * surgeryCapPullback g Q.map y v -
            g0.metric.inner y (v 0) (v 1)) j) x := by
      unfold RiemannianMetric.tensorNorm
      rw [heq]
      rfl
    rw [hn]
    exact (Q.covariant_error_lt (hsub hx) (hj.trans horder)).le
  have hscalar := (scalar_ricciNormSq_eq_of_local_isometry DE D hV
    (a.contMDiffOn.mono hVa) (fun y hy => hinv y (hVa hy))
    (fun y hy v w => congrArg (fun B => B v w) (hmetric y hy)) hxV).1
  rw [hscalar]
  exact abs_scalarCurvature_le_of_metric_error g0.connection DE x Q.eta_pos.le
    hsmall hK (hcurv x) herror




theorem exists_global_initial_chart_scalar_bound
    {g0 : StandardInitialMetric} (estimate : StandardCapEstimate g0) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (S : GeneralizedSliceCarrier.{u})
      (g : RiemannianMetric 3 S.carrier) (tip : S.carrier) (scale eta : ℝ)
      (Q : SurgeryCapClose g0 S g tip scale eta), eta ≤ 1 / 4 →
      ∀ {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
        [T2Space N] (h : RiemannianMetric 3 N) (D : LeviCivitaData h)
        (a : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞),
      a.source ⊆ g0.metric.ball 0 eta⁻¹ →
      EqOn (h.pullbackCoefficients a) Q.normalizedCoefficients a.source →
      ∀ y ∈ a.target, D.scalarCurvature y ≤ M := by
  obtain ⟨K, hK, hcurv⟩ := estimate.curvature_derivative_bounds 0
  simp only [LeviCivitaData.curvatureDerivativeNorm_zero] at hcurv
  refine ⟨72 * (K + 3), by linarith, ?_⟩
  intro S g tip scale eta Q hsmall N _ _ _ _ h D a hsub hlink y hy
  have hb := scalar_bound_of_normalized_comparison Q hsmall hK hcurv h D a hsub hlink
    (a.map_target hy)
  rw [a.right_inv hy] at hb
  exact (le_abs_self _).trans hb

end PoincareConjecture.M44

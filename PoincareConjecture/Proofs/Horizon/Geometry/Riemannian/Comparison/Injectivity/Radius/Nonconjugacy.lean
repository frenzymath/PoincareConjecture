import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Nonconjugacy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isCompact_closure_ball_of_metricComplete (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (R : ℝ) :
    IsCompact (closure (g.ball p R)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply (g.isCompact_closedBall_of_metricComplete hc p R).of_isClosed_subset isClosed_closure
  apply closure_minimal (fun q h => (show g.edist p q < ENNReal.ofReal R from h).le)
  exact isClosed_le (continuous_const.edist continuous_id) continuous_const

theorem injective_mfderiv_globalExponential_of_tangentNorm_lt
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (p : M) {v : EuclideanSpace ℝ (Fin n)}
    (hv : g.tangentNorm p v < Poincare.ODE.Jacobi.comparisonRadius K) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) (g.globalExponential hc p) v) := by
  let R := Poincare.ODE.Jacobi.comparisonRadius K + 1
  have hR : 0 < R := by dsimp [R]; linarith [Poincare.ODE.Jacobi.comparisonRadius_pos K]
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hb⟩ :=
    g.exists_precompact_exponential_with_differential_bounds D p hR hK
      (g.isCompact_closure_ball_of_metricComplete hc p R) (fun x _ => hcurv x)
  have hnorm : ‖L.symm v‖ = g.tangentNorm p v := by
    simpa only [L.apply_symm_apply] using
      (g.tangentNorm_orthonormal_frame p L hL (L.symm v)).symm
  have hvmem : L.symm v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hv.trans (by dsimp [R]; linarith)
  have heq : g.globalExponential hc p =ᶠ[𝓝 v] e ∘ L.symm := by
    filter_upwards [L.symm.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hvmem)] with w hw
    simpa only [L.apply_symm_apply, Function.comp_apply] using
      g.globalExponential_eq_radial_exponential hc p hR L e he0 hed
        (fun u hu => (hgeo u hu).1) hw
  have hediff := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hvmem)).mdifferentiableAt
    (by simp)
  have hLdiff : MDifferentiableAt (𝓡 n) (𝓡 n) L.symm v :=
    (contMDiffAt_iff_contDiffAt.mpr
      (L.symm.contDiff.contDiffAt : ContDiffAt ℝ ∞ L.symm v)).mdifferentiableAt (by simp)
  rw [heq.mfderiv_eq, mfderiv_comp v hediff hLdiff, mfderiv_eq_fderiv, L.symm.fderiv]
  exact (hb _ hvmem (by rw [hnorm]; exact hv.le)).1.1.comp L.symm.injective

end PoincareConjecture.RiemannianMetric

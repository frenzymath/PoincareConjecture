import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.PointedLimit











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold


theorem scalar_lower_bound_le_mul_base_curvatureTensorNorm
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hzero : 0 ∈ Ioo T' T)
    {c : ℝ}
    (hscalar : ∀ᶠ k in atTop,
      c ≤ ((S.flow k).flow.connection 0).scalarCurvature (S.flow k).base) :
    c ≤ (n : ℝ) ^ 2 *
      (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base := by
  apply ge_of_tendsto (tendsto_const_nhds.mul
    (G.tendsto_curvatureTensorNorm 0 hzero G.limitFlow.base) (a := (n : ℝ) ^ 2))
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hscalar] with k hk
  rw [congrArg Prod.snd (G.base_preserving k)]
  exact hk.trans ((le_abs_self _).trans
    (((S.flow (G.subsequence k)).flow.connection 0).abs_scalarCurvature_le_curvatureTensorNorm
      (S.flow (G.subsequence k)).base))


theorem le_base_curvatureTensorNorm_of_eventually
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hzero : 0 ∈ Ioo T' T)
    {c : ℝ}
    (hcurv : ∀ᶠ k in atTop,
      c ≤ ((S.flow k).flow.connection 0).curvatureTensorNorm (S.flow k).base) :
    c ≤ (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base := by
  apply ge_of_tendsto (G.tendsto_curvatureTensorNorm 0 hzero G.limitFlow.base)
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hcurv] with k hk
  rwa [congrArg Prod.snd (G.base_preserving k)]

end PoincareConjecture.PointedGeometricConvergence

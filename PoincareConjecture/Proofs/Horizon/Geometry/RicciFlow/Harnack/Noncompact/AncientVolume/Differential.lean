import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.BoundedFlow

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

theorem PoincareConjecture.RicciFlow.ancient_differential_of_bounded_ancient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : PoincareConjecture.RicciFlowCurvatureTheory.{u})
    (F : PoincareConjecture.RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, PoincareConjecture.MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (_hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR (Iic 0) t ∧
        0 ≤ dR + 2 * mvfderiv (𝓡 n) (F.connection t).scalarCurvature x v +
          2 * (F.connection t).ricci x v v := by
  exact Poincare.RicciFlow.Harnack.ancient_differential_of_bounded_curvature
    hC F hcomplete hoperator hbound

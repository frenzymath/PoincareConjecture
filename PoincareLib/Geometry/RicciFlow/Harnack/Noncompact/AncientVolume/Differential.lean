import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.BoundedFlow

/-!
# Bounded ancient differential Harnack

The ancient-volume hypotheses specialize the complete bounded-flow theorem.
That theorem constructs exhaustion from buffered Shi estimates, proves
Hamilton block positivity, and sends the finite time origin to minus infinity.
No per-slice Harnack theorem is used.

Source: Kleiner--Lott, corrected 2013, Appendix F, pp. 2850--2851,
and Proposition 41.13, p. 2678.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

/-- The full differential inequality under the ancient-volume hypotheses. -/
theorem PoincareMT.RicciFlow.ancient_differential_of_bounded_ancient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : PoincareMT.RicciFlowCurvatureCalculus.{u})
    (F : PoincareMT.RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, PoincareMT.MetricComplete (F.metric t))
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

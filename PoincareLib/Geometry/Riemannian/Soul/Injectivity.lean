import PoincareLib.Geometry.Riemannian.Soul.Exhaustion
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.Radius.Compact
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.Radius.ConvexDescent
import PoincareLib.Analysis.Calculus.Monotonicity.CompactDescent

/-!
# Uniform injectivity under bounded nonnegative curvature

A proper convex Busemann exhaustion has a compact zero set. The canonical
truncated injectivity radius has a positive minimum there. Stationary
descent of a short cut loop propagates this lower bound to the whole
manifold, by minimizing the radius plus a small multiple of the exhaustion.

This proves the needed smooth injectivity consequence of
Maeder-Baumdicker--Seidel, Theorem 1 and Remark 1.1, p. 4; the exhaustion
and descent arguments are in Lemma 3.13, pp. 17--19, and Lemma 5.1,
pp. 35--37. No soul or injectivity hypothesis is supplied.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The canonical injectivity radius, truncated below half the curvature
comparison scale, has a positive uniform lower bound. -/
theorem exists_pos_le_truncatedInjectivityRadius_of_nonnegativeSectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : D.NonnegativeSectionalCurvature)
    {K C : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (hC : 0 < C) (hCK : 2 * C ≤ Poincare.ODE.Jacobi.comparisonRadius K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : M, r ≤ g.truncatedInjectivityRadius hc C x := by
  classical
  let p : M := Classical.arbitrary M
  obtain ⟨f, hf, hfp, hfnonneg, _, hfcompact, hfconvex⟩ :=
    g.exists_continuous_convex_exhaustion D hc hsec p
  have hCK' : C ≤ Poincare.ODE.Jacobi.comparisonRadius K := by linarith
  obtain ⟨m, hm, hcore⟩ := g.exists_pos_le_truncatedInjectivityRadius_on_isCompact
    D hc hK hcurv hC hCK' (hfcompact 0)
  have hzero : ∀ x, f x = 0 → m ≤ g.truncatedInjectivityRadius hc C x := by
    intro x hx
    exact hcore x (show f x ≤ 0 from hx.le)
  refine ⟨min m C, lt_min hm hC, ?_⟩
  apply Poincare.lower_bound_of_stationary_descent
    (g.lowerSemicontinuous_truncatedInjectivityRadius D hc hK hcurv hC hCK')
    hf hfnonneg hfcompact hzero
  intro x hx _
  exact g.exists_stationary_radius_descent_of_convex D hc f p hfp hfnonneg hfconvex
    hK hC hCK hcurv hzero x hx

/-- Bounded nonnegative curvature supplies a fixed positive tangent-ball
radius on which every complete exponential is injective. -/
theorem exists_uniform_injOn_globalExponential_of_nonnegativeSectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : D.NonnegativeSectionalCurvature)
    {K : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Poincare.ODE.Jacobi.comparisonRadius K ∧
      ∀ x : M, InjOn (g.globalExponential hc x) {v | g.tangentNorm x v < r} := by
  let C := Poincare.ODE.Jacobi.comparisonRadius K / 2
  have hC : 0 < C := half_pos (Poincare.ODE.Jacobi.comparisonRadius_pos K)
  have hCK : 2 * C ≤ Poincare.ODE.Jacobi.comparisonRadius K := by dsimp [C]; linarith
  obtain ⟨r, hr, hradius⟩ :=
    g.exists_pos_le_truncatedInjectivityRadius_of_nonnegativeSectional D hc hsec
      hK hcurv hC hCK
  have hrC : r ≤ C := (hradius (Classical.arbitrary M)).trans
    (g.truncatedInjectivityRadius_le hc hC.le _)
  refine ⟨r, hr, hrC.trans (by linarith), ?_⟩
  intro x
  exact (g.injOn_globalExponential_truncatedInjectivityRadius hc hC.le x).mono
    fun v hv => hv.trans_le (hradius x)

end PoincareMT.RiemannianMetric

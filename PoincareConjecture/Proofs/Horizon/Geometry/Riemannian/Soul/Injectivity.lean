import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.ConvexDescent
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Monotonicity.CompactDescent

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

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

end PoincareConjecture.RiemannianMetric

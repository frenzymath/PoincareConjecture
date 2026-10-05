import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.Radius.LowerSemicontinuity

/-!
# Positive injectivity bounds on compact sets

The lower semicontinuous canonical truncated radius attains a positive
minimum on each nonempty compact set. This supplies the compact-core bound in
Maeder--Baumdicker--Seidel, arXiv:2310.03369v3, Lemma 5.1, p. 35.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A nonempty compact set contains a point minimizing the positive
truncated injectivity radius. -/
theorem exists_min_truncatedInjectivityRadius_on_isCompact
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {K C : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (hC : 0 < C) (hCK : C ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) :
    ∃ p ∈ S, 0 < g.truncatedInjectivityRadius hc C p ∧
      ∀ q ∈ S, g.truncatedInjectivityRadius hc C p ≤ g.truncatedInjectivityRadius hc C q := by
  have hlsc := g.lowerSemicontinuous_truncatedInjectivityRadius D hc hK hcurv hC hCK
  obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hSne hS
    (hlsc.lowerSemicontinuousOn S)
  exact ⟨p, hp, g.truncatedInjectivityRadius_pos hc hC p, hmin⟩

/-- The canonical truncated injectivity radius has a strictly positive
uniform lower bound on every compact set. -/
theorem exists_pos_le_truncatedInjectivityRadius_on_isCompact
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {K C : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (hC : 0 < C) (hCK : C ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    {S : Set M} (hS : IsCompact S) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ S, r ≤ g.truncatedInjectivityRadius hc C p := by
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst S
    exact ⟨1, zero_lt_one, by simp⟩
  · obtain ⟨p, _, hp, hmin⟩ :=
      g.exists_min_truncatedInjectivityRadius_on_isCompact D hc hK hcurv hC hCK hS hSne
    exact ⟨g.truncatedInjectivityRadius hc C p, hp, hmin⟩

end PoincareMT.RiemannianMetric

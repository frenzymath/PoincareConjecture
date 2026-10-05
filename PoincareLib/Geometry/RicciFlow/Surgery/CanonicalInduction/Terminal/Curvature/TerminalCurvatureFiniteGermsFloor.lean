import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureFiniteGermsBound

/-!
# A unit-floored terminal curvature bound from finite germs

The finite-germ terminal consumer returns a positive full-curvature bound.
This adapter only floors that bound by one for the downstream scalar and
common-interval producers.
Source: derivations/terminal-curvature-finite-germs-bridge.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M47

/-- The reviewed finite-germ terminal bound, normalized to a bound at least
one for downstream duration and scalar estimates. -/
theorem terminalCurvature_bound_of_finite_germs_floor
    {epsilon1 epsilon A H : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1)
    (hcalibrated : epsilon ≤ 1 / 200) (hA : 0 < A)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (p : M) (hscalar : D.scalarCurvature p ≠ 0)
    {ι : Type*} (U : ι → Opens M) [∀ i, ConnectedSpace (U i)]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 3) y),
      ((F i).metric 0).inner y v w = g.inner y.val v w)
    (hlocalOperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ y,
      ((F i).connection t).NonnegativeCurvatureOperator y)
    (htriple : ∀ x y z : M, ∃ i, x ∈ U i ∧ y ∈ U i ∧ z ∈ U i)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨
        IsCompact (univ : Set M)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x, D.curvatureTensorNorm x ≤ K := by
  obtain ⟨B, hB, hbound⟩ := terminalCurvature_bound_of_finite_germs
    hM45 hepsilon hsmall hcalibrated hA D hC hcomplete hoperator p hscalar U tau htau F
      hmetric hlocalOperator htriple hreadout
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro x
  exact hbound x |>.trans (le_max_right _ _)

end PoincareMT.M47

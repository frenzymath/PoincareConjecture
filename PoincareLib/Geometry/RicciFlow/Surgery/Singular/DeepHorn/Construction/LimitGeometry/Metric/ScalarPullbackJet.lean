import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Scalar.ScalarJets
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

/-!
# The scalar two-jet on an actual local parametrization

Morgan--Tian Claim 11.34, printed pp. 288-289, and Claim 11.35, p. 290.
The local realization argument of the eligible M07
`jetRicci_metricTwoJet_pullback` identifies the genuine metric two-jet.
The owned scalar trace and the eligible M12
`LeviCivitaData.scalarCurvature_eq_of_local_isometry` then identify its
value with the supplied connection's scalar curvature. Reviewed derivation:
`claim11_34-slice-curvature-comparison.md`, section 2.
-/

set_option autoImplicit false
-- The Euclidean and manifold tangent instances agree in the native two-jet.
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M32

open SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The native scalar trace of the actual pullback metric two-jet equals
the retained scalar curvature on the certified parametrization domain.
Source: Claim 11.34, pp. 288-289, and Claim 11.35, p. 290;
`claim11_34-slice-curvature-comparison.md`, section 2. -/
theorem scalarMetricTraceTwoJet_pullback
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {phi : EuclideanSpace ℝ (Fin n) → M}
    (hphi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ phi U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) phi y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    scalarMetricTraceTwoJet (metricTwoJet (g.pullbackCoefficients phi) x) =
      D.scalarCurvature (phi x) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients phi) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients
      (hphi.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients phi) hcoeff (fun y _ u v => g.symm (phi y) _ _)
    (fun y hy w hw => by
      apply g.pos (phi y)
      intro hz
      apply hw
      apply (hinv y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (phi y)
        (mfderiv (𝓡 n) (𝓡 n) phi y u) (mfderiv (𝓡 n) (𝓡 n) phi y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients phi := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← metricTwoJet_congr_of_eventuallyEq hB, scalarMetricTraceTwoJet_metricTwoJet DE]
  exact DE.scalarCurvature_eq_of_local_isometry D hV (hphi.mono hVU) hmetric hxV

end PoincareMT.M32

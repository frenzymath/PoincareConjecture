import PoincareConjecture.Proofs.M32.Claim11_35.ScalarJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

open SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

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

end PoincareConjecture.M32

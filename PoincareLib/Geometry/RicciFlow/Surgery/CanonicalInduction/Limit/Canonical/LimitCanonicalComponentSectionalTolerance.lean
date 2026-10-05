import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalComponentPlaneReadout
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalComponentJetMargin
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ScalarFourJet

/-!
# One sectional tolerance from an actual compact source chart

The actual old sectional bound supplies every native model-plane margin.
Compactness fixes its two-jet tolerance before any perturbed field.
MT Definition 9.75 and Proposition 17.1, pp. 231 and 407-408;
limit-canonical-component-sectionals.md, B2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

open M04 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance componentToleranceCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance componentToleranceCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace
noncomputable local instance componentToleranceTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup
noncomputable local instance componentToleranceTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

/-- Actual strict sectional bounds on one compact chart give a single
native two-jet tolerance for every point and every model plane. -/
theorem limitCanonical_component_sectional_jet_tolerance
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {K : Set E} (hK : IsCompact K) (hKsource : K ⊆ f.source) (a : ℝ)
    (hsec : ∀ x ∈ K, ∀ u v : TangentSpace (𝓡 3) (f x),
      LeviCivitaData.IsOrthonormalPair g (f x) u v → a < D.sectionalCurvature (f x) u v) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ K, ∀ J : MetricTwoJet 3,
      ‖J - metricTwoJet (g.pullbackCoefficients f) x‖ ≤ delta →
      ∀ p ∈ modelOrthonormalPairs 3, J ∈ sectionalJetLowerRegion a p.1 p.2 := by
  have hJ : ContinuousOn (metricTwoJet (g.pullbackCoefficients f)) K := by
    intro x hx
    exact (contDiffAt_metricTwoJet (g.contDiffAt_pullbackCoefficients
      (f.contMDiffOn_toFun.contMDiffAt
        (f.open_source.mem_nhds (hKsource hx))))).continuousAt.continuousWithinAt
  obtain ⟨delta, hdelta, hbound⟩ := limitCanonical_exists_uniform_sectional_jet_margin
    hK (isCompact_modelOrthonormalPairs 3) (metricTwoJet (g.pullbackCoefficients f)) hJ a
    (fun x hx p hp => limitCanonical_component_model_jet_lower D f
      (hKsource hx) a (hsec x hx) p hp)
  exact ⟨delta, hdelta, fun x hx J hnear p hp => hbound x hx p hp J hnear⟩

end PoincareMT.M47

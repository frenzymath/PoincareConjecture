import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsCapJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Evolution.FamilyJetsCylinder

/-!
# The actual ordinary and cap comparison coefficients agree

The reconstructed ordinary flow and the literal cap comparison use the
same spatial pullback and the same height normalization. Their equality
on the open birth source identifies every coordinate two-jet.
Source: Morgan--Tian Corollary 16.9 and Claim 16.10, pp. 373-375.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance capCoefficientsNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capCoefficientsSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
  {J : Set ℝ} {U : Set (F.slice t).carrier}
  (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
  (initial : SurgeryCapInitialComparison F t hT i A)
  (G : M44.CylinderRicciFlow e (capInitialPartialDiffeomorph initial))
  (hmap : (capInitialPartialDiffeomorph initial).target ⊆ U)
  (p : (⟨(capInitialPartialDiffeomorph initial).target,
    (capInitialPartialDiffeomorph initial).open_target⟩ : Opens (F.slice t).carrier))

include hmap

/-- Both normalized coefficient fields are identical on the actual
birth chart, including both differential slots. -/
theorem cap_ordinary_coefficients_eq (s : ℝ) (hs : s ∈ J)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    (G.flow.metric s).pullbackCoefficients
      (M44.targetChart (capInitialPartialDiffeomorph initial) p) x =
        capComparisonCoefficients e initial.chart s hs x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact (G.pullback_eq_cylinder hmap p s hs hx v w).trans
    (capComparisonCoefficients_apply e initial.chart s hs x v w).symm

/-- The open-source coefficient equality identifies the full native
two-jet, without any regularity assertion outside that source. -/
theorem cap_ordinary_twoJet_eq (s : ℝ) (hs : s ∈ J)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    metricTwoJet ((G.flow.metric s).pullbackCoefficients
      (M44.targetChart (capInitialPartialDiffeomorph initial) p)) x =
        metricTwoJet (capComparisonCoefficients e initial.chart s hs) x := by
  have heq : (G.flow.metric s).pullbackCoefficients
      (M44.targetChart (capInitialPartialDiffeomorph initial) p) =ᶠ[𝓝 x]
        capComparisonCoefficients e initial.chart s hs := by
    filter_upwards [(capInitialPartialDiffeomorph initial).open_source.mem_nhds hx] with y hy
    exact cap_ordinary_coefficients_eq e initial G hmap p s hs hy
  simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
    (heq.fderiv (𝕜 := ℝ)).fderiv_eq]

end PoincareMT.M47

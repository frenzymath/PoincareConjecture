import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Construction
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Construction
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Assembly
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Inheritance
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Monotonicity

/-!
# A complete normalized closed limit on the original carrier

Uniform source control produces the actual closed flow, with completeness,
the original noncollapse constant, curvature positivity, scalar normalization,
and past curvature control. Global boundedness remains a separate geometric
step before packaging this flow as an ancient kappa-solution.

Reference: Morgan--Tian, Theorem 9.64, pp. 225-229.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance closedLimitConnected (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

/-- The normalized sequence has an actual complete closed ancient limit
on its retained interior carrier, before any global curvature bound is used. -/
theorem exists_complete_noncollapsed_closed_geometric_limit
    {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hlocal : M23LocalCurvatureEstimate S) :
    ∃ G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
        (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1,
      ∃ F : RicciFlow 3 G.limitCarrier.carrier (Iic 0),
        (∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1)) ∧
        (∀ t : ℝ, t ≤ 0 → G.limitCarrier.metricComplete (F.metric t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ x : G.limitCarrier.carrier,
          (F.connection t).NonnegativeCurvatureOperator x) ∧
        AncientKappaNoncollapsed F κ ∧
        (F.connection 0).scalarCurvature G.base = 1 ∧
        (∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : G.limitCarrier.carrier,
          (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x) ∧
        (∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : G.limitCarrier.carrier,
          |(F.connection s).curvatureTensorNorm x| ≤ (F.connection t).scalarCurvature x) := by
  have hcontrol := m23AllTimeCurvatureControl_of_local S P hlocal
  obtain ⟨G, hcomplete, _, _, _⟩ :=
    S.exists_complete_noncollapsed_interior_geometric_limit P hlocal
  have hreference := hcomplete 0 (by norm_num)
  obtain ⟨F, hF⟩ := S.exists_terminal_flow_on_interior_carrier G P hcontrol hreference
  exact ⟨G, F, hF, S.closedLimit_complete G F hF P hcontrol hreference,
    S.closedLimit_nonnegativeCurvatureOperator G P F hF,
    S.closedLimit_noncollapsed G P hcomplete F hF,
    S.closedLimit_scalar_normalized G P hcontrol F hF,
    S.closedLimit_scalar_monotone G P F hF,
    fun s t hst ht x => S.closedLimit_past_norm_le_scalar G P F hF hst ht x⟩

end PoincareMT.NormalizedKappaSolutionSequence

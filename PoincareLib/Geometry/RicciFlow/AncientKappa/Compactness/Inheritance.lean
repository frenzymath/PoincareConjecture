import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Windows
import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareLib.Geometry.RicciFlow.Compactness.Assembly
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source

/-!
# Geometric properties of the retained normalized ancient limit

Finite windows retain the same ancient metric and connection. The normalized
source sequence supplies radius-dependent two-time curvature bounds, so
completeness of the reference slice propagates to every interior time.
Nonnegative curvature operator passes to that same limit from the sources.

Reference: Morgan--Tian, Theorem 9.64, pp. 225-229; Kleiner--Lott,
Appendix E, Corollary E.2, pp. 2848-2849.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance inheritanceSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace

variable (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
  (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

/-- Every interior slice of the retained normalized limit has nonnegative
curvature operator. -/
theorem interiorLimit_nonnegativeCurvatureOperator :
    ∀ t : ℝ, t < 1 → ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  apply G.nonnegativeCurvatureOperator_of_eventually F (by norm_num) ?_ ?_
  · intro a b hb
    exact Eventually.of_forall fun k t ht => by
      change t - 1 ≤ 0
      linarith [ht.2]
  · intro t ht
    change t < 1 at ht
    exact Eventually.of_forall fun k x =>
      (S.term k).flow.nonnegative_curvature_operator (t - 1) (by linarith) x

/-- Reference-slice completeness propagates to every interior time using
the radius-dependent two-time bounds inherited on one finite window. -/
theorem interiorLimit_complete
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t) := by
  intro t ht
  obtain ⟨a, b, ha, hb, hb1, htw⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_singleton (singleton_subset_iff.mpr ht)
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo a b ⊆ (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro u hu
    change u - 1 ≤ 0
    linarith [hu.2]
  let selected : NormalizedKappaSolutionSequence kappa :=
    ⟨S.kappa_pos, fun k => S.term (G.subsequence k)⟩
  have hselected : M23AllTimeCurvatureControl selected := by
    intro r hr
    obtain ⟨C, hC, hbound⟩ := hcontrol r hr
    exact ⟨C, hC, fun k => hbound (G.subsequence k)⟩
  let H := selected.compactnessHypotheses P hselected ha hb hb1.le
  let W : PointedGeometricConvergence H.sequence :=
    G.window F (ha.trans hb) hb1.le 0 hsub
  exact W.complete_interior hcomplete t (htw (mem_singleton t))

end PoincareMT.NormalizedKappaSolutionSequence

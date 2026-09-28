import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance inheritanceSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace

variable (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
  (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)



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

end PoincareConjecture.NormalizedKappaSolutionSequence

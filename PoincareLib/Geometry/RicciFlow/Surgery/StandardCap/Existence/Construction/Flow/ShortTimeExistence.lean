import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Curvature.InitialFlowCurvature
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.InitialFlowCompleteness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.ScalarPositivity

/-!
# Short-time partial standard-cap existence

For every supplied standard initial metric, compact doubles and the
fixed-coordinate endpoint limit construct a genuine complete flow on
a positive half-open slab, retaining the prescribed initial metric and
connection and one global full-curvature bound. This is the short-time
construction in Morgan-Tian Theorem 12.5, p. 297; maximal continuation
and unit lifetime are separate obligations.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The constructed initial slab fills every field of the frozen partial
standard-cap flow structure (Theorem 12.5, p. 297). -/
noncomputable def InteriorCoefficientLimit.partialFlow
    {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
    (G : InteriorCoefficientLimit A) (P : RicciFlowCurvatureTheory.{0}) :
    PartialStandardCapFlow g0 where
  lifetime := A.time
  lifetime_pos := A.time_pos
  flow := G.initialFlow P
  initial_metric := G.initialFlow_metric_zero P
  initial_connection := G.initialFlow_connection_zero P
  curvature_locally_bounded := by
    intro T0 _hT0 hT0T
    refine ⟨A.curvature_bound 0, (A.bound_pos 0).le, ?_⟩
    intro t ht x
    exact G.initialFlow_abs_curvature_le P ⟨ht.1, ht.2.trans_lt hT0T⟩ x

/-- Every supplied standard initial metric has an actual complete
positive-time partial Ricci flow with globally bounded full curvature
(Theorem 12.5, p. 297). -/
theorem completePartialStandardCapFlow_exists (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) :
    ∃ F : PartialStandardCapFlow g0,
      (∀ t ∈ Ico 0 F.lifetime, MetricComplete (F.flow.metric t)) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ico 0 F.lifetime, ∀ x : StandardCapSpace,
        |(F.flow.connection t).curvatureTensorNorm x| ≤ K := by
  obtain ⟨E0⟩ := standardCapEstimate_exists g0
  obtain ⟨A⟩ := compactCapApproximation_exists P g0 E0
  obtain ⟨G⟩ := interiorCoefficientLimit_exists A P.curvature
  refine ⟨G.partialFlow P.curvature, ?_, A.curvature_bound 0, A.bound_pos 0, ?_⟩
  · exact fun _ ht => G.initialFlow_complete P.curvature ht
  · exact fun _ ht x => G.initialFlow_abs_curvature_le P.curvature ht x

end PoincareMT.M34

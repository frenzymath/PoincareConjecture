import PoincareConjecture.Proofs.M35.Thm12_28.BlowupSequence
import PoincareConjecture.Proofs.M09.RiemannianProper

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem isCompact_closure_ball (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    {t : ℝ} (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (p : (slice (Ico 0 E.flow.base.lifetime) t).carrier) (r : ℝ) :
    IsCompact (closure ((metric E.flow.base.flow t).ball p r)) := by
  let : ConnectedSpace (slice (Ico 0 E.flow.base.lifetime) t).carrier :=
    (sliceDiffeomorph ht).toHomeomorph.connectedSpace_iff.mpr inferInstance
  exact Proofs.M09.isCompact_closure_metric_ball (metric E.flow.base.flow t)
    ((complete_iff P E.flow.base.flow ht).mpr (E.complete t ht)) p r

theorem blowupSequence_balls_compact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop) :
    BlowupBaseBallsCompact (blowupSequence P E t x ht hR) := by
  intro A _
  exact Eventually.of_forall (fun k => isCompact_closure_ball P E (ht k) _ _)

end PoincareConjecture.M35.OrdinaryRealization

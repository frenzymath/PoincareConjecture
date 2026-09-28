import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Transport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryRegularSlab

open SurgeryEventRebuild

variable {past future : ℝ → SliceMetric.{u}} {a b : ℝ}
  (A : SurgeryRegularSlab (fun t => (past t).1) (fun t => (past t).2) a b)
  (h : Set.EqOn past future (Set.Icc a b))

private theorem initial_pair (A : SurgeryRegularSlab
    (fun t => (past t).1) (fun t => (past t).2) a b)
    (h : Set.EqOn past future (Set.Icc a b)) : past a = future a :=
  h ⟨le_rfl, A.ordered.le⟩

def copyFamily : SurgeryRegularSlab
    (fun t => (future t).1) (fun t => (future t).2) a b where
  ordered := A.ordered
  flow := SurgeryEventRebuild.flow (initial_pair A h) A.flow
  identify t := diffeomorph (initial_pair A h) (h t.property) (A.identify t)
  initial_identify := by
    intro x
    obtain ⟨y, rfl⟩ := (SurgeryEventRebuild.identify
      (past a) (future a) (initial_pair A h)).surjective x
    exact (diffeomorph_apply (initial_pair A h) (initial_pair A h)
      (A.identify ⟨a, le_rfl, A.ordered.le⟩) y).trans
      (congrArg (SurgeryEventRebuild.identify (past a) (future a) (initial_pair A h))
        (A.initial_identify y))
  metric_pullback t x v w :=
    diffeomorph_flow_metric_pullback (initial_pair A h) (h t.property)
      A.flow t (A.identify t) (A.metric_pullback t) x v w

theorem copyFamily_flow_heq : HEq (A.copyFamily h).flow A.flow :=
  flow_heq (initial_pair A h) A.flow

theorem copyFamily_identify_apply (t : Set.Icc a b) (x : (past a).1.carrier) :
    (A.copyFamily h).identify t
        (SurgeryEventRebuild.identify (past a) (future a) (initial_pair A h) x) =
      SurgeryEventRebuild.identify (past t) (future t) (h t.property) (A.identify t x) :=
  diffeomorph_apply (initial_pair A h) (h t.property) (A.identify t) x

theorem copyFamily_transport (s t : Set.Icc a b) (x : (past s).1.carrier) :
    (A.copyFamily h).transport s t
        (SurgeryEventRebuild.identify (past s) (future s) (h s.property) x) =
      SurgeryEventRebuild.identify (past t) (future t) (h t.property) (A.transport s t x) := by
  have hs := A.copyFamily_identify_apply h s ((A.identify s).symm x)
  simp only [Diffeomorph.apply_symm_apply] at hs
  rw [← hs]
  simp only [SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply]
  exact A.copyFamily_identify_apply h t _

end PoincareConjecture.SurgeryRegularSlab

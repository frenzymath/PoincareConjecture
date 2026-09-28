import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_ObservedCages
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_21_ObservedAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M46

theorem capAvoidanceProducer_of_parameters
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (rNext : ℝ) (_hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (rho : ℝ) (hrho : 0 < rho) (_hrho_le : rho ≤ rNext)
    (params : ActionBarrierParameters S p rho) (cutoff : ℝ)
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon params.c (rho / 2)) :
    CapAvoidanceProducer.{u} p rNext cutoff rho params.A params.eta params.theta := by
  intro F O inputs D H hnew hradius caps
  have hceiling : D.time ≤ surgeryEpochStart (p.i + 1) :=
    D.time_mem.2.le.trans inputs.next_epoch.2
  have hstart : 0 ≤ surgeryEpochStart (p.i - 1) := by
    unfold surgeryEpochStart
    positivity
  have hordered : surgeryEpochStart (p.i - 1) < D.time := by
    have hmargin := (prefix_old_time_bounds p hnew hceiling).1
    linarith
  have hwindow : Icc 0 D.time ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    exact fun _ hs => hs
  have henergy : 0 ≤ 2 * positiveActionBudget p :=
    mul_nonneg (by norm_num) (positiveActionBudget_pos p).le
  apply actionConfinement_of_local_surgery_cages H.spacetime.history H.spacetime.geometry
    hstart hordered hwindow (actionBudget_large p hceiling) henergy
  · intro tau _htau hbound y path haction
    exact observed_path_squareEnergy_le P p inputs.old inputs.next_epoch H path hbound haction
  · apply exists_observed_surgery_cages P S p hp hrLast hrho params hcutoff
      inputs D H hradius caps
    intro tau _htau hbound y path haction
    exact observed_path_positiveAction_le P p inputs.old inputs.next_epoch H path hbound haction

end PoincareConjecture.Proofs.M46

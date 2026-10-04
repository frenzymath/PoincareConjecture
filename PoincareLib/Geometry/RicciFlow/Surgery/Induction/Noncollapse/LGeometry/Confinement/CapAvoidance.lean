import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.Confinement.ObservedCages
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.ObservedAction

/-!
# The actual cap-avoidance producer for Proposition 16.1

Lemma 16.15 and Proposition 16.21, pp. 379-387. Uniform positive action
excludes the persistent cap windows; their actual compact birth and
post-slab sets, the global square-time modulus, and the finite time
cover then confine every admissible path below the fixed action barrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.Proofs.M46

/-- The literal producer required by the final induction assembly.
All numerical cap parameters precede the observed flow, and the final
cutoff retains the scalar separation on the auxiliary test scale.
Source: Proposition 16.1 and Lemma 16.15, pp. 367-368 and 379-382. -/
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

end PoincareMT.Proofs.M46

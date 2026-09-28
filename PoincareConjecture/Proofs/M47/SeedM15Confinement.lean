import PoincareConjecture.Proofs.M47.SeedM15Cages
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ObservedWindow

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem exists_seedM15_confinementCutoff
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext rho : ℝ} (hrNext : 0 < rNext)
    (hrLast : rNext ≤ p.r (Fin.last p.i)) (hrho : 0 < rho) :
    ∃ params : ActionBarrierParameters S p rho, ∃ cutoff : ℝ,
      0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ∀ _inputs : ObservedInputs p rNext cutoff F O,
            ∀ (T r : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
              (x : (F.slice T).carrier) (H : SeedM15TestHistory T hT hTF x r),
              surgeryEpochStart p.i ≤ T → T ≤ O.H →
              SeedM15SafeCylinder H rho params.safeTime params.safeTime_pos →
                ∃ C : ActionConfinement H.spacetime.geometry.toLGeometry T
                  (surgeryEpochStart (p.i - 1))
                  ((H.spacetime.geometry.sliceIdentification T).identification H.center).val,
                    C.barrier = actionBudget p := by
  obtain ⟨params⟩ := exists_actionBarrierParameters S p hrho
  have htheta : 0 < params.theta := by linarith [params.theta_half]
  obtain ⟨capCutoff, hcapCutoff, hlast, hcaps⟩ :=
    exists_seedCompatibleOverlapCapCutoff S p hp rNext hrNext hrLast
      params.A params.eta params.theta params.A_pos params.eta_pos htheta params.theta_one
  let cutoff := min capCutoff (capScalarCutoff p.setup.epsilon params.c (rho / 2))
  have hsmall : cutoff ≤ capCutoff := min_le_left _ _
  have hscalar : cutoff ≤ capScalarCutoff p.setup.epsilon params.c (rho / 2) :=
    min_le_right _ _
  have hcutoff : 0 < cutoff := lt_min hcapCutoff
    (capScalarCutoff_pos p.setup.epsilon_pos params.c_pos (half_pos hrho))
  refine ⟨params, cutoff, hcutoff, hsmall.trans hlast, ?_⟩
  intro F O inputs T r hT hTF x H hnew hTH safe
  let larger := inputs.cutoff_mono hsmall
  have caps : OverlapCapControl p O inputs.old params.A params.eta params.theta :=
    hcaps F O inputs.next_epoch inputs.old inputs.admissible inputs.pinched
      larger.scales inputs.canonical larger.overlap
  exact seedM15_actionConfinement P S p hp hrLast hrho params hscalar
    inputs H hnew hTH safe caps

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M47.SeedM15Confinement
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CapBirth

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_cap_birth_floor
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff rho : ℝ} (params : ActionBarrierParameters S p rho)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    (caps : OverlapCapControl p O inputs.old params.A params.eta params.theta) :
    ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ y ∈ ((F.event t hT).caps i).carrier,
        params.c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature y := by
  intro t hT hn ht hstart i
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [inputs.old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo inputs.old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (redecorateTo_standard_flow O inputs.old.standard_initial_eq).trans hpflow
  have htheta : 0 < params.theta := by linarith [params.theta_half]
  have hA : F.standard_initial.cylindrical_end.radius + 5 < params.A := by
    rw [hinitial]
    linarith [params.A_buffer, params.A_pos]
  apply insertedCap_scalarLower_of_persistence
    (O.redecorateTo inputs.old.standard_initial_eq) hT i htheta hA ht.2
    (fun J U e initial comparison => params.scalar_bound F hinitial _ hmodel
      t hT hn i J U e initial comparison
        (F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))))
  exact caps t hT ht hstart i

theorem exists_seedM15_commonCutoff
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext rho : ℝ} (hrNext : 0 < rNext)
    (hrLast : rNext ≤ p.r (Fin.last p.i)) (hrho : 0 < rho)
    (params : ActionBarrierParameters S p rho) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      cutoff ≤ capScalarCutoff p.setup.epsilon params.c rNext ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        (inputs : ObservedInputs p rNext cutoff F O),
        OverlapCapControl p O inputs.old params.A params.eta params.theta ∧
        (∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
          t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
          ∀ i : Fin (F.event t hT).cap_count,
          ∀ y ∈ ((F.event t hT).caps i).carrier,
            params.c / (2 * (F.parameters.h t) ^ 2) ≤
              (F.connection t).scalarCurvature y) ∧
        ∀ (T r : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
          (x : (F.slice T).carrier) (H : SeedM15TestHistory T hT hTF x r),
          surgeryEpochStart p.i ≤ T → T ≤ O.H →
          SeedM15SafeCylinder H rho params.safeTime params.safeTime_pos →
            ∃ C : ActionConfinement H.spacetime.geometry.toLGeometry T
              (surgeryEpochStart (p.i - 1))
              ((H.spacetime.geometry.sliceIdentification T).identification H.center).val,
                C.barrier = actionBudget p := by
  have htheta : 0 < params.theta := by linarith [params.theta_half]
  obtain ⟨capCutoff, hcapCutoff, hlast, hcaps⟩ :=
    exists_seedCompatibleOverlapCapCutoff S p hp rNext hrNext hrLast
      params.A params.eta params.theta params.A_pos params.eta_pos htheta params.theta_one
  let scalarCutoff := min (capScalarCutoff p.setup.epsilon params.c (rho / 2))
    (capScalarCutoff p.setup.epsilon params.c rNext)
  let cutoff := min capCutoff scalarCutoff
  have hsmall : cutoff ≤ capCutoff := min_le_left _ _
  have hscalar : cutoff ≤ capScalarCutoff p.setup.epsilon params.c (rho / 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hseed : cutoff ≤ capScalarCutoff p.setup.epsilon params.c rNext :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcutoff : 0 < cutoff := lt_min hcapCutoff
    (lt_min (capScalarCutoff_pos p.setup.epsilon_pos params.c_pos (half_pos hrho))
      (capScalarCutoff_pos p.setup.epsilon_pos params.c_pos hrNext))
  refine ⟨cutoff, hcutoff, hsmall.trans hlast, hseed, ?_⟩
  intro F O inputs
  let larger := inputs.cutoff_mono hsmall
  have caps : OverlapCapControl p O inputs.old params.A params.eta params.theta :=
    hcaps F O inputs.next_epoch inputs.old inputs.admissible inputs.pinched
      larger.scales inputs.canonical larger.overlap
  refine ⟨caps, seedM15_cap_birth_floor S p hp params inputs caps, ?_⟩
  intro T r hT hTF x H hnew hTH safe
  exact seedM15_actionConfinement P S p hp hrLast hrho params hscalar
    inputs H hnew hTH safe caps

end PoincareConjecture.M47

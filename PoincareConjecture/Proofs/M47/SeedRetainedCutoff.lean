import PoincareConjecture.Proofs.M47.SeedRetainedConfinement
import PoincareConjecture.Proofs.M47.SeedM15CapFloor









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem exists_seedRetained_commonCutoff
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
          ∀ b ∈ Icc (-T) 0,
          ∀ U : TopologicalSpace.Opens (F.slice T).carrier,
          IsCompact (U : Set (F.slice T).carrier) → x ∈ U →
          ∀ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U,
          (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
          b < -3 * params.safeTime →
            ∃ C : ActionConfinement H.spacetime.geometry.toLGeometry T
              (surgeryEpochStart (p.i - 1))
              ((H.spacetime.geometry.sliceIdentification T).identification H.center).val,
                C.barrier = actionBudget p := by
  obtain ⟨base, hbase, hlast, hscalar, hcommon⟩ :=
    exists_seedM15_commonCutoff P S p hp hrNext hrLast hrho params
  let timeCutoff := Real.sqrt params.safeTime / (2 * p.setup.epsilon)
  have htime : 0 < timeCutoff := div_pos (Real.sqrt_pos.mpr params.safeTime_pos)
    (mul_pos (by norm_num) p.setup.epsilon_pos)
  let cutoff := min base (min 1 timeCutoff)
  have hcutoff : 0 < cutoff := lt_min hbase (lt_min zero_lt_one htime)
  have hbaseLe : cutoff ≤ base := min_le_left _ _
  have hone : cutoff ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htimeLe : cutoff ≤ timeCutoff := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, hcutoff, hbaseLe.trans hlast, hbaseLe.trans hscalar, ?_⟩
  intro F O inputs
  let larger := inputs.cutoff_mono hbaseLe
  obtain ⟨caps, hfloor, _⟩ := hcommon F O larger
  refine ⟨caps, hfloor, ?_⟩
  intro T r hT hTF x H hnew hTH b hb U hcompact hx e hbased hage
  exact seedRetained_actionConfinement P S p hp hrLast params hone htimeLe inputs
    H hnew hTH hb U hcompact hx e hbased hage caps

end PoincareConjecture.M47

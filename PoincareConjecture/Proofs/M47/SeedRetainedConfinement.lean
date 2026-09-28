import PoincareConjecture.Proofs.M47.SeedRetainedCompact
import PoincareConjecture.Proofs.M47.SeedRetainedOldCages










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem seedRetained_actionConfinement
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff rho : ℝ} (hrLast : rNext ≤ p.r (Fin.last p.i))
    (params : ActionBarrierParameters S p rho)
    (hcutoffOne : cutoff ≤ 1)
    (hcutoffTime : cutoff ≤ Real.sqrt params.safeTime / (2 * p.setup.epsilon))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r)
    (hnew : surgeryEpochStart p.i ≤ T) (hTH : T ≤ O.H)
    {b : ℝ} (hb : b ∈ Icc (-T) 0)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier)) (hx : x ∈ U)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hage : b < -3 * params.safeTime)
    (caps : OverlapCapControl p O inputs.old params.A params.eta params.theta) :
    ∃ C : ActionConfinement H.spacetime.geometry.toLGeometry T
      (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val,
        C.barrier = actionBudget p := by
  have hceiling : T ≤ surgeryEpochStart (p.i + 1) := hTH.trans inputs.next_epoch.2
  have hstart : 0 ≤ surgeryEpochStart (p.i - 1) := by unfold surgeryEpochStart; positivity
  have hordered : surgeryEpochStart (p.i - 1) < T := by
    have hmargin := (prefix_old_time_bounds p hnew hceiling).1
    linarith
  have hwindow : Icc 0 T ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    exact fun _ hs => hs
  have hinterval : Icc (T + b) T ⊆ H.spacetime.history.generalized.interval := by
    apply Subset.trans _ hwindow
    exact Icc_subset_Icc (by linarith [hb.1]) le_rfl
  obtain ⟨K, hK, hcapture⟩ := seedRetained_compact_path_trace H.spacetime U hcompact
    e hinterval hbased H.time_mem H.center ⟨x, hx⟩ H.center_eq hage
    (show -3 * params.safeTime < 0 by linarith [params.safeTime_pos])
  let Z := actionSublevelTrace H.spacetime.geometry.toLGeometry T
    (surgeryEpochStart (p.i - 1))
    ((H.spacetime.geometry.sliceIdentification T).identification H.center).val (actionBudget p)
  have hrecent : ∀ v ∈ Z, T - 2 * params.safeTime ≤ v.1 → v ∈ K := by
    rintro v ⟨tau, htau, hbound, y, path, haction, age, hage, rfl⟩ hclock
    have hpath := path.curve_time age hage
    change (path.curve age).1 = T - age at hpath
    apply hcapture path hage
    rw [hpath] at hclock
    linarith [params.safeTime_pos]
  apply actionConfinement_of_local_surgery_cages H.spacetime.history H.spacetime.geometry
    hstart hordered hwindow (actionBudget_large p hceiling)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (positiveActionBudget_pos p).le)
  · intro tau _htau hbound y path haction
    exact seedM15_path_squareEnergy_le P p H inputs.pinched hceiling path hbound haction
  · intro t ht htSurgery
    by_cases htold : t < T - 2 * params.safeTime
    · exact seedRetained_older_surgery_cages P S p hp hrLast params hcutoffOne
        hcutoffTime inputs H hTH caps ht htSurgery htold
    · have htrecent : T - 2 * params.safeTime ≤ t := le_of_not_gt htold
      refine ⟨K, hK, ?_, K, hK, (T - t) / 2, by linarith [ht.2], ?_⟩
      · intro v hv hvt
        exact hrecent v hv (hvt.symm ▸ htrecent)
      · intro v hv hvt
        exact hrecent v hv (htrecent.trans hvt.1)

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M47.SeedM15Action
import PoincareConjecture.Proofs.M47.SeedM15CapWindow
import PoincareConjecture.Proofs.M47.SeedM15InitialCapture
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_ObservedCages

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_surgery_cages
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff rho : ℝ} (hrLast : rNext ≤ p.r (Fin.last p.i)) (hrho : 0 < rho)
    (params : ActionBarrierParameters S p rho)
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon params.c (rho / 2))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r) (hTH : T ≤ O.H)
    (safe : SeedM15SafeCylinder H rho params.safeTime params.safeTime_pos)
    (caps : OverlapCapControl p O inputs.old params.A params.eta params.theta) :
    ∀ t ∈ Ico (surgeryEpochStart (p.i - 1)) T, t ∈ F.surgery_times →
      ∃ K : Set H.spacetime.history.generalized.point, IsCompact K ∧
        (∀ v ∈ actionSublevelTrace H.spacetime.geometry.toLGeometry T
          (surgeryEpochStart (p.i - 1))
          ((H.spacetime.geometry.sliceIdentification T).identification H.center).val
          (actionBudget p), v.1 = t → v ∈ K) ∧
        ∃ N : Set H.spacetime.history.generalized.point, IsCompact N ∧
          ∃ delta : ℝ, 0 < delta ∧
            ∀ v ∈ actionSublevelTrace H.spacetime.geometry.toLGeometry T
              (surgeryEpochStart (p.i - 1))
              ((H.spacetime.geometry.sliceIdentification T).identification H.center).val
              (actionBudget p), v.1 ∈ Icc t (t + delta) → v ∈ N := by
  classical
  have hceiling : T ≤ surgeryEpochStart (p.i + 1) := hTH.trans inputs.next_epoch.2
  have hwindow : Icc 0 T ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    exact fun _ hs => hs
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [inputs.old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo inputs.old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (redecorateTo_standard_flow O inputs.old.standard_initial_eq).trans hpflow
  have htheta : 0 < params.theta := by linarith [params.theta_half]
  have hbuffer : F.standard_initial.cylindrical_end.radius + 5 < params.A / 2 := by
    rw [hinitial]
    exact params.A_buffer
  have scales := inputs.old.capPersistenceScales inputs.next_epoch.2 hrLast
    inputs.scales inputs.overlap
  intro t ht htSurgery
  have ht0 : 0 ≤ t := F.time_domain_nonnegative (F.surgery_times_subset htSurgery)
  have htime : t ∈ H.spacetime.history.generalized.interval := hwindow ⟨ht0, ht.2.le⟩
  have htobs : t ∈ surgeryObservationInterval O := ⟨ht0, ht.2.trans_le hTH⟩
  have hn : Nonempty (F.slice t).carrier :=
    (F.closedRegularHistoryWindow T hT hTF ⟨x⟩).slice_nonempty t ⟨ht0, ht.2.le⟩
  let : CompactSpace (F.slice t).carrier :=
    isCompact_univ_iff.mp (F.slices_compact t (F.surgery_times_subset htSurgery))
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t ht0
  have hseparation : 9 * rho⁻¹ ^ 2 < params.c / (2 * (F.parameters.h t) ^ 2) := by
    have hdelta : F.parameters.delta t ≤
        capScalarCutoff F.parameters.epsilon params.c (rho / 2) := by
      rw [inputs.old.epsilon_eq]
      exact (scales.delta_le t ⟨htobs, ht.1⟩).trans hcutoff
    have hfloor := cap_birth_floor_gt_four_inv_sq F ht0 params.c_pos (half_pos hrho) hdelta
    have hratio : 4 * (rho / 2)⁻¹ ^ 2 = 16 * rho⁻¹ ^ 2 := by
      field_simp [hrho.ne']
      ring
    rw [hratio] at hfloor
    nlinarith [sq_pos_of_pos (inv_pos.mpr hrho)]
  have hwindows (i : Fin (F.event t htSurgery).cap_count) :
      ∃ Q : CapBarrierWindow H.spacetime.geometry (F.slice t) (F.metric t)
        ((F.event t htSurgery).caps i).tip t T params.A (F.parameters.h t)
        params.c params.mu params.theta,
          Nonempty (CapBarrierOriginData H.spacetime.history Q) := by
    apply seedM15_capBarrierWindow H.spacetime.history H.spacetime.geometry
      P.m13 (O.redecorateTo inputs.old.standard_initial_eq) htSurgery i ht.2 hTH
      htheta hwindow
    · intro J U e initial comparison hzero s hs hst y hy v
      exact params.metric_bound F hinitial _ hmodel t J U e initial.chart comparison
        hzero s hs hst y hy v
    · intro J U e initial comparison s hs hst y hy
      exact params.scalar_bound F hinitial _ hmodel t htSurgery hn i J U e initial comparison
        hh s hs hst y hy
    · exact caps t htSurgery htobs ht.1 i
  choose Q hQ using hwindows
  let origin := fun i => Classical.choice (hQ i)
  let Z := actionSublevelTrace H.spacetime.geometry.toLGeometry T
    (surgeryEpochStart (p.i - 1))
    ((H.spacetime.geometry.sliceIdentification T).identification H.center).val (actionBudget p)
  have havoid : ∀ v ∈ Z, ∀ i, v ∉ (Q i).earlyInnerTrace := by
    rintro v ⟨tau, htau, hbound, y, path, haction, b, hb, rfl⟩ i ⟨w, hi, hearly, heq⟩
    have hbudget := seedM15_path_positiveAction_le P p H inputs.pinched hceiling
      path hbound haction
    have hscalar := safe.initial_scalar_bound P.m12 hrho params.safeTime_action path hbudget
    exact (Q i).avoids_early_inner_of_initial_scalar P.m12 params.mu_pos params.A_pos hh
      params.c_pos params.theta_one (positiveActionBudget_pos p).le params.safeTime_pos
      params.side_barrier params.top_barrier hseparation path hscalar hbudget hb
      w hi hearly heq.symm
  have hbirth : ∀ y : (H.spacetime.history.generalized.slice t).carrier,
      (⟨t, y⟩ : H.spacetime.history.generalized.point) ∈ Z →
        H.spacetime.history.history.forward t htime y ∈
          surgeryCapExcludedSlice F t htSurgery (params.A / 2) := by
    intro y hy hbad
    obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
    obtain ⟨tau, htau, hbound, z, path, haction, b, hb, heq⟩ := hy
    have hbudget := seedM15_path_positiveAction_le P p H inputs.pinched hceiling
      path hbound haction
    have hscalar := safe.initial_scalar_bound P.m12 hrho params.safeTime_action path hbudget
    have hclock : T - b = t := by
      have hpath := path.curve_time b hb
      change (path.curve b).1 = T - b at hpath
      exact hpath.symm.trans (congrArg Sigma.fst heq)
    have hbpos : 0 < b := by linarith [ht.2]
    have hi' : H.spacetime.history.history.forward t htime y ∈
        (F.metric t).ball ((F.event t htSurgery).caps i).tip
          (params.A * F.parameters.h t / 2) := by
      have hrad : params.A / 2 * F.parameters.h t = params.A * F.parameters.h t / 2 := by
        ring
      simpa only [hrad] using hi
    exact (origin i).avoids_birth_of_initial_scalar H.spacetime.history (Q i) P.m12
      params.mu_pos params.A_pos hh params.c_pos params.theta_one
      (positiveActionBudget_pos p).le params.safeTime_pos params.side_barrier
      params.top_barrier hseparation path hscalar hbudget ⟨hbpos, hb.2⟩ hclock htime y hi' heq
  obtain ⟨hK, hregular⟩ := surgeryCapExcludedSlice_compact_regular F t htSurgery hbuffer
  obtain ⟨hcompact, hcapture⟩ := regularSliceLift_compact H.spacetime.history htime hK hregular
  refine ⟨_, hcompact, ?_, ?_⟩
  · rintro ⟨s, y⟩ hv hclock
    change s = t at hclock
    subst s
    exact hcapture y (hbirth y hv)
  · exact exists_compact_postSurgery_cage H.spacetime.history H.spacetime.geometry
      htSurgery ht.2 hwindow hbuffer Q origin havoid hbirth

theorem seedM15_actionConfinement
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff rho : ℝ} (hrLast : rNext ≤ p.r (Fin.last p.i)) (hrho : 0 < rho)
    (params : ActionBarrierParameters S p rho)
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon params.c (rho / 2))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r)
    (hnew : surgeryEpochStart p.i ≤ T) (hTH : T ≤ O.H)
    (safe : SeedM15SafeCylinder H rho params.safeTime params.safeTime_pos)
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
  apply actionConfinement_of_local_surgery_cages H.spacetime.history H.spacetime.geometry
    hstart hordered hwindow (actionBudget_large p hceiling)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (positiveActionBudget_pos p).le)
  · intro tau _htau hbound y path haction
    exact seedM15_path_squareEnergy_le P p H inputs.pinched hceiling path hbound haction
  · exact seedM15_surgery_cages P S p hp hrLast hrho params hcutoff inputs H hTH safe caps

end PoincareConjecture.M47

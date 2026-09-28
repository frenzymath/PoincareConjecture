import PoincareConjecture.Proofs.M47.SeedM15Cages
import PoincareConjecture.Proofs.M47.SeedRetainedCapAvoidance









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem seedRetained_height_sq_le
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {rNext cutoff a : ℝ} (ha : 0 < a)
    (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoffOne : cutoff ≤ 1)
    (hcutoffTime : cutoff ≤ Real.sqrt a / (2 * p.setup.epsilon))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {t : ℝ} (ht : t ∈ surgeryObservationInterval O)
    (htold : surgeryEpochStart (p.i - 1) ≤ t) :
    (F.parameters.h t) ^ 2 ≤ a / 4 := by
  have scales := inputs.old.capPersistenceScales inputs.next_epoch.2 hrLast
    inputs.scales inputs.overlap
  have hdelta := scales.delta_le t ⟨ht, htold⟩
  have hd0 := (F.parameters.delta_pos t ht.1).le
  have hd1 := hdelta.trans hcutoffOne
  have hdsq : (F.parameters.delta t) ^ 2 ≤ F.parameters.delta t := by
    nlinarith only [hd0, hd1]
  have htime := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
    p.setup.epsilon_pos)).mp (hdelta.trans hcutoffTime)
  have hde : F.parameters.delta t * F.parameters.epsilon ≤ Real.sqrt a / 2 := by
    rw [inputs.old.epsilon_eq]
    nlinarith only [htime]
  have hh : F.parameters.h t ≤ Real.sqrt a / 2 := calc
    _ ≤ (F.parameters.delta t) ^ 2 * F.parameters.r t := F.parameters.h_le t ht.1
    _ ≤ F.parameters.delta t * F.parameters.r t :=
      mul_le_mul_of_nonneg_right hdsq (F.parameters.r_pos t ht.1).le
    _ ≤ F.parameters.delta t * F.parameters.epsilon :=
      mul_le_mul_of_nonneg_left (F.parameters.r_le_epsilon t ht.1) hd0
    _ ≤ _ := hde
  nlinarith only [hh, (F.parameters.h_pos t ht.1).le,
    Real.sqrt_nonneg a, Real.sq_sqrt ha.le]



theorem seedRetained_older_surgery_cages
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext cutoff rho : ℝ} (hrLast : rNext ≤ p.r (Fin.last p.i))
    (params : ActionBarrierParameters S p rho)
    (hcutoffOne : cutoff ≤ 1)
    (hcutoffTime : cutoff ≤ Real.sqrt params.safeTime / (2 * p.setup.epsilon))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r) (hTH : T ≤ O.H)
    (caps : OverlapCapControl p O inputs.old params.A params.eta params.theta)
    {t : ℝ} (ht : t ∈ Ico (surgeryEpochStart (p.i - 1)) T)
    (htSurgery : t ∈ F.surgery_times) (htold : t < T - 2 * params.safeTime) :
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
  have ht0 : 0 ≤ t := F.time_domain_nonnegative (F.surgery_times_subset htSurgery)
  have htime : t ∈ H.spacetime.history.generalized.interval := hwindow ⟨ht0, ht.2.le⟩
  have htobs : t ∈ surgeryObservationInterval O := ⟨ht0, ht.2.trans_le hTH⟩
  have hn : Nonempty (F.slice t).carrier :=
    (F.closedRegularHistoryWindow T hT hTF ⟨x⟩).slice_nonempty t ⟨ht0, ht.2.le⟩
  let : CompactSpace (F.slice t).carrier :=
    isCompact_univ_iff.mp (F.slices_compact t (F.surgery_times_subset htSurgery))
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t ht0
  have hheight := seedRetained_height_sq_le p params.safeTime_pos hrLast
    hcutoffOne hcutoffTime inputs htobs ht.1
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
  have htop (i) : (Q i).top ≤ T - params.safeTime := by
    have hthetaH := mul_le_mul_of_nonneg_right params.theta_one.le
      (sq_nonneg (F.parameters.h t))
    nlinarith only [(Q i).top_le_model, hthetaH, hheight, htold, params.safeTime_pos]
  let Z := actionSublevelTrace H.spacetime.geometry.toLGeometry T
    (surgeryEpochStart (p.i - 1))
    ((H.spacetime.geometry.sliceIdentification T).identification H.center).val (actionBudget p)
  have havoid : ∀ v ∈ Z, ∀ i, v ∉ (Q i).earlyInnerTrace := by
    rintro v ⟨tau, htau, hbound, y, path, haction, b, hb, rfl⟩ i ⟨w, hi, hearly, heq⟩
    have hbudget := seedM15_path_positiveAction_le P p H inputs.pinched hceiling
      path hbound haction
    exact seedRetained_avoids_early_cap (Q i) P.m12 params.mu_pos params.A_pos hh
      params.c_pos params.theta_one (positiveActionBudget_pos p).le params.safeTime_pos
      params.side_barrier params.top_barrier (htop i) path hbudget hb w hi hearly heq.symm
  have hbirth : ∀ y : (H.spacetime.history.generalized.slice t).carrier,
      (⟨t, y⟩ : H.spacetime.history.generalized.point) ∈ Z →
        H.spacetime.history.history.forward t htime y ∈
          surgeryCapExcludedSlice F t htSurgery (params.A / 2) := by
    intro y hy hbad
    obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
    obtain ⟨tau, htau, hbound, z, path, haction, b, hb, heq⟩ := hy
    have hbudget := seedM15_path_positiveAction_le P p H inputs.pinched hceiling
      path hbound haction
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
    exact seedRetained_avoids_cap_birth H.spacetime.history (Q i) (origin i) P.m12
      params.mu_pos params.A_pos hh params.c_pos params.theta_one
      (positiveActionBudget_pos p).le params.safeTime_pos params.side_barrier
      params.top_barrier (htop i) path hbudget ⟨hbpos, hb.2⟩ hclock htime y hi' heq
  obtain ⟨hK, hregular⟩ := surgeryCapExcludedSlice_compact_regular F t htSurgery hbuffer
  obtain ⟨hcompact, hcapture⟩ := regularSliceLift_compact H.spacetime.history htime hK hregular
  refine ⟨_, hcompact, ?_, ?_⟩
  · rintro ⟨s, y⟩ hv hclock
    change s = t at hclock
    subst s
    exact hcapture y (hbirth y hv)
  · exact exists_compact_postSurgery_cage H.spacetime.history H.spacetime.geometry
      htSurgery ht.2 hwindow hbuffer Q origin havoid hbirth

end PoincareConjecture.M47

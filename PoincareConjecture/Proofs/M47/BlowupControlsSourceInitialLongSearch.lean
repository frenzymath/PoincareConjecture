import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOverlap
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapCutoff
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapDisjoint
import PoincareConjecture.Proofs.M47.PrefixMonotone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_old_long_search
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {m M R etaNeg : ℝ} (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hetaNeg : 0 < etaNeg) :
    ∃ L d Q0 : ℝ, 1 ≤ L ∧ 2 / m ≤ L ∧ 0 < d ∧ d ≤ m ∧ d ≤ 1 ∧ 0 < Q0 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ _prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
        ∀ {base Q : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q →
          rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
        ∀ (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
          (i : Fin (F.event T hT).cap_count) (old : SurgeryTerminalStrongNeck F T hT i),
          Q * (base - T) ∈ Icc (0 : ℝ) 1 →
          m ≤ Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) →
          Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) ≤ M →
        let N := ((F.event T hT).necks i).neck
        let q := N.scale⁻¹ ^ 2
        let H := Q / q
        let u := -1 + d / (4 * H)
        let c := H * (u + 1 / 2)
        let shift := -(Q * (base - T)) - H / 2
        let phi := fun s : ℝ => -1 / 2 + s / H
        let V := N.region (-R) R
        ∃ hc : c < 0, ∃ (b : ℝ) (_hb : b ∈ Icc (c - 2 * d) c),
          ∃ E : SurgeryFlowCylinder F (F.event T hT).terminal
              (base + shift / Q) Q (Icc b 0) V,
            (∀ s ∈ Icc c 0, phi s ∈ Ioo (-1 : ℝ) 0) ∧
            (∀ s (_hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0)
                (hraw : phi s ∈ Ioo (-1 : ℝ) 0),
              (⟨(base + shift / Q) + s / Q, E.forward s hs'⟩ :
                (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier)) =
                ⟨T + phi s / q, old.cylinder.forward (phi s) hraw⟩) ∧
            (∀ s (hs : s ∈ Icc b c), ∀ x ∈ V,
              (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
                (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x) ≤ 4 * L * Q ∧
              |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
                (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x)| ≤ (13 * max (4 * L) 1) * Q ∧
              (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
                (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x) ≤ etaNeg * Q) ∧
            phi b < -1 - 3 * d / (4 * M) := by
  obtain ⟨deltaOld, hdeltaOld, hdeltaSmall, disjointTolerance⟩ :=
    exists_source_initial_cap_disjoint_tolerance S.cap_persistence hR.le
  let A := 2 * (S.standard_initial.cylindrical_end.radius + 5) + 1
  have hA : 2 * (S.standard_initial.cylindrical_end.radius + 5) < A := by
    dsimp only [A]
    linarith
  have hArate : S.standard_initial.cylindrical_end.radius + 5 < A := by
    linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨etaGeo, hetaGeo, _hetaGeoSmall, noContact⟩ := disjointTolerance A hA
  obtain ⟨rate, hrate, rateTolerance⟩ := exists_source_initial_cap_anchor_cutoff S p hp
  obtain ⟨etaRate, hetaRate, _hetaRateSmall, capCutoff⟩ :=
    rateTolerance (1 / 2) (by norm_num) (by norm_num) A hArate
  let eta := min etaGeo etaRate
  have heta : 0 < eta := lt_min hetaGeo hetaRate
  obtain ⟨L, d, hL, hmL, hd, hdm, hdOne, hshort, hDuration⟩ :=
    exists_source_initial_search_cap_duration (blowupAnalyticConstant_pos S B) hm hrate
      (by norm_num : (0 : ℝ) < 1 / 2)
  let Q0 := max 128 (max (64 * (M + 4))
    (max B.curvature_threshold (blowupPinchingThreshold (4 * L) etaNeg)))
  have hQ0 : 0 < Q0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨L, d, Q0, hL, hmL, hd, hdm, hdOne, hQ0, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaCap, hdeltaCap, hdeltaLast, anchor⟩ :=
    capCutoff eta heta (min_le_right _ _) rNext hrNext hrLast
  let deltaB := B.delta S.setup.standard_initial S.constants
  let cutoff := min deltaCap (min deltaOld deltaB)
  have hcutoff : 0 < cutoff := lt_min hdeltaCap (lt_min hdeltaOld (B.delta_pos _ _))
  have hcutCap : cutoff ≤ deltaCap := min_le_left _ _
  have hcutOld : cutoff ≤ deltaOld := (min_le_right _ _).trans (min_le_left _ _)
  have hcutB : cutoff ≤ deltaB := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, hcutoff, hcutCap.trans hdeltaLast, ?_⟩
  intro F O hH prior hadmissible hpinched next overlap base Q hBase hLarge hThreshold
    hEarlier T hT hnT i old hage hmH hHM
  let N := ((F.event T hT).necks i).neck
  let q := N.scale⁻¹ ^ 2
  let H := Q / q
  let u := -1 + d / (4 * H)
  let c := H * (u + 1 / 2)
  let shift := -(Q * (base - T)) - H / 2
  let phi := fun s : ℝ => -1 / 2 + s / H
  let V := N.region (-R) R
  have h128 : 128 ≤ Q := (le_max_left _ _).trans hLarge
  have hQ : 0 < Q := by linarith only [h128]
  have hScale : 64 * (M + 4) ≤ Q :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hLarge
  have hBthreshold : B.curvature_threshold ≤ Q :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLarge
  have hPinchingScale : blowupPinchingThreshold (4 * L) etaNeg ≤ Q :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLarge
  have hTOverlap := source_initial_recent_time_mem_overlap p hBase hH h128 hage
  have hdelta : F.parameters.delta T ≤ deltaOld := (overlap T hTOverlap).trans hcutOld
  have hsmall : F.parameters.delta T ≤ 1 / 200 :=
    hdelta.trans (hdeltaSmall.trans (by norm_num))
  have hInitial : F.standard_initial = S.setup.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  have hOverlapB : ∀ t ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants := by
    intro t ht
    exact (overlap t ⟨ht.1, ht.2.1, ht.2.2.trans_le hH⟩).trans hcutB
  obtain ⟨hc, b, hb, E, hraw, hread, hbounds, hstop⟩ :=
    exists_source_initial_old_bounded_search S B p P hm hd hdm hdOne hL hmL hshort hetaNeg
      O hInitial prior.local_constants_eq hC hBase hScale hBthreshold hThreshold hpinched
      hEarlier hOverlapB hPinchingScale hT i old hsmall hage hmH hHM hR
  change b ∈ Icc (c - 2 * d) c at hb
  refine ⟨hc, b, hb, E, hraw, hread, hbounds, ?_⟩
  rcases hstop with hlong | ⟨hbshort, _hbirthOld, hEvent, hcap⟩
  · exact hlong
  exfalso
  let bottom : b ∈ Icc b 0 := ⟨le_rfl, hb.2.trans hc.le⟩
  let birth := (base + shift / Q) + b / Q
  let h := F.parameters.h birth
  let sigma := (c - b) / (Q * h ^ 2)
  let : Nonempty (F.slice birth).carrier := ⟨E.forward b bottom N.center⟩
  obtain ⟨j, y, hyImage, hyCap⟩ := hcap
  obtain ⟨x, hx, hxy⟩ := hyImage
  have hxCap : E.forward b bottom x ∈ ((F.event birth hEvent).caps j).carrier :=
    hxy.symm ▸ hyCap
  have hHpos : 0 < H := hm.trans_le hmH
  have hShift : shift ≤ 0 := by
    dsimp only [shift]
    linarith only [hage.1, hHpos]
  obtain ⟨_hu, _hu34, _hshiftRaw, hbuffer, _hlong⟩ :=
    source_initial_search_anchor_bounds hm hd hdm hdOne hmH hHM hage
  have hsum : shift + c = -(Q * (base - T)) + H * u := by
    dsimp only [shift, c]
    ring
  have hwindow : -(M + 3) ≤ shift + b := by
    change -(M + 3) ≤ -(Q * (base - T)) + H * u - 2 * d at hbuffer
    rw [← hsum] at hbuffer
    linarith only [hbuffer, hb.1]
  have hScale' : 64 * ((M + 3) + 1) ≤ Q := by linarith only [hScale]
  have hscalar := (hbounds b ⟨le_rfl, hb.2⟩ x hx).1
  obtain ⟨_hfloor, cap, initial, comparison, based, hAnchor, hSigmaHalf, hContact⟩ :=
    anchor F O hH prior hadmissible hpinched (next.mono_delta hcutCap)
      (fun t ht => (overlap t ht).trans hcutCap) hBase
      (by linarith only [hM] : 0 ≤ M + 3) hScale' hEarlier hShift hwindow E
      (N.region_isOpen (-R) R) hc hbshort (zero_lt_one.trans_le hL) hDuration
      hEvent j x hx hxCap hscalar
  have hzero : (0 : ℝ) ∈ Ico 0 (surgeryCapDuration birth (base + shift / Q) h (1 / 2)) :=
    ⟨le_rfl, hAnchor.1.trans_lt hAnchor.2⟩
  have hrawC := hraw c ⟨le_rfl, hc.le⟩
  have hreadC := hread c ⟨le_rfl, hc.le⟩ ⟨hb.2, hc.le⟩ hrawC
  have hpoint := congrArg (fun p :
      (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier) =>
        (⟨p.1, p.2 x⟩ : Σ t, (F.slice t).carrier)) hreadC
  have hcontactFull := hContact.trans hpoint
  have hdeltaNeck : N.epsilon = F.parameters.delta T := (F.event T hT).neck_delta i
  have hNsmall : N.epsilon ≤ deltaOld := hdeltaNeck.trans_le hdelta
  have hclose := old.comparison.at_time ⟨hrawC.1, hrawC.2.le⟩
  rw [if_neg hrawC.2.ne] at hclose
  have hclose' : RoundCylinderClose N.epsilon (phi c)
      (surgeryCylinderPullback old.cylinder N.coordinate_map (phi c)) :=
    hdeltaNeck.symm ▸ hclose
  have hinitial : F.standard_initial = S.standard_initial :=
    hInitial.trans S.setup_standard_initial_eq
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo prior.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
  exact noContact F hinitial _ hmodel N old.cylinder hNsmall (phi c) hrawC hrawC hclose'
    birth hEvent j _ cap initial eta heta (min_le_left _ _) comparison
    hzero (based hzero) sigma hAnchor (by linarith only [hSigmaHalf])
    (E.forward b bottom x) hxCap x hx hcontactFull

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M47.CanonicalNeckFirstFailureCap
import PoincareConjecture.Proofs.M47.CanonicalNeckExposedStandardCap
import PoincareConjecture.Proofs.M47.CanonicalStandardTipLocus
import PoincareConjecture.Proofs.M47.CanonicalCapCompactFamily










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47




theorem exists_firstFailure_exposed_physical_cap_cutoff_of_standard_cover
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {epsilonOut C : ℝ} (hC : 0 < C)
    (cover : ∀ s ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        ((S.cap_persistence.standard_cap.flow.metric s).edist 0 x).toReal *
          Real.sqrt ((S.cap_persistence.standard_cap.flow.connection s).scalarCurvature x) ≤
            (57 / 10 : ℝ) * S.setup.epsilon⁻¹ →
        ∃ N : CapCertificate (S.cap_persistence.standard_cap.flow.metric s),
          N.epsilon = epsilonOut ∧ N.cap_constant ≤ C ∧
          N.connection = S.cap_persistence.standard_cap.flow.connection s ∧ x ∈ N.core) :
    ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ _old : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
        ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
          SurgeryCanonicalOn F (Ico 0 T) rNext →
        ∀ (N : SurgeryStrongNeck F T F.parameters.epsilon),
          rNext⁻¹ ^ 2 ≤ (F.connection T).scalarCurvature N.neck.center →
        ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
          (U : Set (F.slice T).carrier) = N.neck.carrier →
        ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
            (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
          (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
          (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
            (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
            ∀ x ∈ U,
              HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
                (N.cylinder.forward s hs x)) →
          let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
          let ha : a ∈ Icc a 0 :=
            ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
          let t := T + a / 1
          ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
          ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
            E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
            ∃ H : CapCertificate (F.metric T),
              H.epsilon = epsilonOut ∧ H.cap_constant ≤ C ∧
              H.connection = F.connection T ∧ N.neck.center ∈ H.core := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, radii⟩ :=
    exists_firstFailure_included_cap_comparison_capture_cutoff_above P S p hp
  have htheta : theta1 < 1 := ht12.trans ht2
  have htheta0 : 0 < theta1 := by linarith only [ht1]
  let K : Set (ℝ × StandardCapSpace) := {z | z.1 ∈ Icc 0 theta1 ∧
    ((S.cap_persistence.standard_cap.flow.metric z.1).edist 0 z.2).toReal *
      Real.sqrt ((S.cap_persistence.standard_cap.flow.connection z.1).scalarCurvature z.2) ≤
        (57 / 10 : ℝ) * S.setup.epsilon⁻¹}
  obtain ⟨R, hR, hcompact, hsub⟩ := exists_compact_standard_tip_locus S.cap_persistence
    htheta0 htheta (mul_nonneg (show (0 : ℝ) ≤ 57 / 10 by norm_num)
      (inv_pos.mpr S.setup.epsilon_pos).le)
  have hcover : ∀ z ∈ K,
      ∃ H : CapCertificate (S.cap_persistence.standard_cap.flow.metric z.1),
        H.epsilon = epsilonOut ∧ H.cap_constant ≤ C ∧
        H.connection = S.cap_persistence.standard_cap.flow.connection z.1 ∧ z.2 ∈ H.core := by
    intro z hz
    apply cover z.1 _ z.2 hz.2
    rw [S.cap_persistence.standard_cap.lifetime_one]
    exact ⟨hz.1.1, hz.1.2.trans_lt htheta⟩
  obtain ⟨A0, _hA0, _hRA0, tolerances⟩ :=
    exists_compact_standard_cap_physical_tolerance_above S.cap_persistence htheta0.le
      htheta hC hR hcompact hsub hcover
  obtain ⟨A, etaI, hA0A, hA, hetaI, _hetaHalf, included⟩ := radii A0
  obtain ⟨etaF, hetaF, transfer⟩ := tolerances A hA0A.le
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  let D := S.cap_persistence.standard_cap.initial_estimate.scalar_constant
  let Acap := S.standard_initial.cylindrical_end.radius + 5
  have hD : 0 < D := S.cap_persistence.standard_cap.initial_estimate.scalar_constant_pos
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [S.standard_initial.cylindrical_end.radius_pos]
  have hfactor : 0 < Real.sqrt D * Acap := mul_pos (Real.sqrt_pos.mpr hD) hAcap
  have heps : S.setup.epsilon ≤ (Real.sqrt D * Acap)⁻¹ :=
    S.calibration.epsilon_source_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsetup : S.setup.epsilon * Real.sqrt D * Acap ≤ 1 := by
    have h := (le_div_iff₀ hfactor).mp
      (show S.setup.epsilon ≤ 1 / (Real.sqrt D * Acap) by simpa only [one_div] using heps)
    simpa only [mul_assoc] using h
  have hsmall : S.setup.epsilon ≤ 1 / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  obtain ⟨etaS, hetaS, _hetaNear, locus⟩ :=
    exists_exposed_neck_standard_cap_locus_tolerance P S.cap_persistence
      S.setup.epsilon_pos hsmall S.calibration.beta_pos S.calibration.beta_lt_half
      htheta hApos hsetup S.calibration.canonical_source
  let eta := min etaI (min etaF etaS)
  have heta : 0 < eta := lt_min hetaI (lt_min hetaF hetaS)
  have hetaI' : eta ≤ etaI := min_le_left _ _
  have hetaF' : eta ≤ etaF := (min_le_right _ _).trans (min_le_left _ _)
  have hetaS' : eta ≤ etaS := (min_le_right _ _).trans (min_le_right _ _)
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, produce⟩ := included eta heta hetaI' rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O hH old admissible pinched scales overlap T hT past N hhigh U hU E hbased hagree
  dsimp only
  intro hSurgery hn i contact hcontact
  obtain ⟨hd, hdt, closed, initial, comparison, based, capture, terminal⟩ :=
    produce F O hH old admissible pinched scales overlap T hT past N hhigh U hU E
      hbased hagree hSurgery i contact hcontact
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hmodel : HEq (O.redecorateTo old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow := by
    apply (M46.redecorateTo_standard_flow O old.standard_initial_eq).trans
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hepsilon : F.parameters.epsilon = S.setup.epsilon := by
    rw [old.epsilon_eq, hp.setup_eq]
  let N0 : SurgeryStrongNeck F T S.setup.epsilon := {
    neck := N.neck
    epsilon_eq := N.epsilon_eq.trans hepsilon
    connection_eq := N.connection_eq
    cylinder := N.cylinder
    terminal_identity := N.terminal_identity
    metric_comparison := by simpa only [hepsilon] using N.metric_comparison }
  obtain ⟨z, hz, hzy, hlocus, _hcap⟩ := locus F hinitial
    (O.redecorateTo old.standard_initial_eq).standard_flow hmodel T N0 U hU E
      hbased hagree hSurgery i contact hcontact hd hdt.le closed initial eta heta hetaS'
        comparison based capture terminal
  let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
  let t := T + a / 1
  let h := F.parameters.h t
  let d := (T - t) / h ^ 2
  have hh : 0 < h := F.parameters.h_pos t
    (F.time_domain_nonnegative (F.surgery_times_subset hSurgery))
  have htop : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  obtain ⟨H, hHe, hHC, hHD, hHcore⟩ := transfer F hinitial
    (O.redecorateTo old.standard_initial_eq).standard_flow hmodel t hSurgery hn i
      (Icc 0 d) _ closed initial eta heta hetaF' comparison hh d htop z
        ⟨⟨hd.le, hdt.le⟩, hlocus.le⟩
  have hclock : t + d / (h⁻¹ ^ 2) = T := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  have hcenter : N.neck.center ∈ (U : Set (F.slice T).carrier) := by
    rw [hU]
    exact N.neck.central_sphere_subset N.neck.center_on_central_sphere
  have hpoint : (⟨t + d / (h⁻¹ ^ 2), actualCapSliceChart closed initial comparison d htop z⟩ :
      Σ s, (F.slice s).carrier) = ⟨T, N.neck.center⟩ := by
    apply Sigma.ext hclock
    change HEq (closed.forward d htop (initial.chart z)) N.neck.center
    rw [hzy]
    exact terminal htop N.neck.center hcenter
  exact (congrArg (fun w : Σ s, (F.slice s).carrier =>
    ∃ H : CapCertificate (F.metric w.1), H.epsilon = epsilonOut ∧ H.cap_constant ≤ C ∧
      H.connection = F.connection w.1 ∧ w.2 ∈ H.core) hpoint).mp
        ⟨H, hHe, hHC, hHD, hHcore⟩

end PoincareConjecture.Proofs.M47

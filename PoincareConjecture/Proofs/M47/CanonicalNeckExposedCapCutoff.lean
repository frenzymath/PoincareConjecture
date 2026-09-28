import PoincareConjecture.Proofs.M47.CanonicalNeckFirstFailureCap
import PoincareConjecture.Proofs.M47.CanonicalNeckExposedStandardCap









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47




theorem exists_firstFailure_exposed_standard_cap_cutoff
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ theta A eta : ℝ,
      1 / 2 < theta ∧ theta < 1 ∧
      S.standard_initial.cylindrical_end.radius + 5 < A ∧
      0 < eta ∧ eta ≤ 1 / 1000 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ old : SurgeryPrefixControls p F O,
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
            let d := (T - t) / (F.parameters.h t) ^ 2
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
              E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
              0 < d ∧ d < theta ∧
                ∃ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
                    (Icc 0 d)
                    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
                  ∃ initial : SurgeryCapInitialComparison F t hT i A,
                    SurgeryCapFamilyComparison F
                      (O.redecorateTo old.standard_initial_eq).standard_flow
                      A eta closed initial.chart ∧
                    (∀ hs z, z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                      (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                    (∀ x ∈ U, E.forward a ha x ∈ (F.metric t).ball
                      ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                    (∀ htop x, x ∈ U →
                      HEq (closed.forward d htop (E.forward a ha x)) x) ∧
                    ∃ z ∈ F.standard_initial.metric.ball 0 A,
                      initial.chart z = E.forward a ha N.neck.center ∧
                      ∃ cap : StandardCapNeighborhood S.cap_persistence.standard_cap.atlas
                          S.cap_persistence.standard_cap.flow d
                          (S.calibration.beta * S.setup.epsilon / 3)
                          S.calibration.Cstandard z,
                        Nonempty (M45StandardCapRefinement cap) := by
  obtain ⟨theta1, theta2, A, etaI, ht1, ht12, ht2, hA, hetaI, _hetaHalf, included⟩ :=
    exists_firstFailure_included_cap_comparison_capture_cutoff P S p hp
  have htheta : theta1 < 1 := ht12.trans ht2
  have hApos : 0 < A := by
    linarith [S.standard_initial.cylindrical_end.radius_pos]
  let D := S.cap_persistence.standard_cap.initial_estimate.scalar_constant
  let Acap := S.standard_initial.cylindrical_end.radius + 5
  have hD : 0 < D := S.cap_persistence.standard_cap.initial_estimate.scalar_constant_pos
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [S.standard_initial.cylindrical_end.radius_pos]
  have hfactor : 0 < Real.sqrt D * Acap := mul_pos (Real.sqrt_pos.mpr hD) hAcap
  have heps : S.setup.epsilon ≤ (Real.sqrt D * Acap)⁻¹ :=
    S.calibration.epsilon_source_le.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hsetup : S.setup.epsilon * Real.sqrt D * Acap ≤ 1 := by
    have h := (le_div_iff₀ hfactor).mp
      (show S.setup.epsilon ≤ 1 / (Real.sqrt D * Acap) by
        simpa only [one_div] using heps)
    simpa only [mul_assoc] using h
  have hsmall : S.setup.epsilon ≤ 1 / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  obtain ⟨etaS, hetaS, hetaNear, standardCap⟩ :=
    exists_exposed_neck_standard_cap_tolerance P S.cap_persistence
      S.setup.epsilon_pos hsmall S.calibration.beta_pos S.calibration.beta_lt_half
      htheta hApos hsetup S.calibration.canonical_source
  let eta := min etaI etaS
  have heta : 0 < eta := lt_min hetaI hetaS
  have hetaI' : eta ≤ etaI := min_le_left _ _
  have hetaS' : eta ≤ etaS := min_le_right _ _
  refine ⟨theta1, A, eta, ht1, htheta, hA, heta, hetaS'.trans hetaNear, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, produce⟩ := included eta heta hetaI' rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O hH old admissible pinched scales overlap T hT past N hhigh U hU
    E hbased hagree
  dsimp only
  intro hSurgery hn i contact hcontact
  obtain ⟨hd, hdt, closed, initial, comparison, based, capture, terminal⟩ :=
    produce F O hH old admissible pinched scales overlap T hT past N hhigh
      U hU E hbased hagree hSurgery i contact hcontact
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
  obtain ⟨z, hz, hzy, ⟨cap⟩⟩ := standardCap F hinitial
    (O.redecorateTo old.standard_initial_eq).standard_flow hmodel T N0 U hU E
      hbased hagree hSurgery i contact hcontact hd hdt.le closed initial eta heta hetaS'
        comparison based capture terminal
  exact ⟨hd, hdt, closed, initial, comparison, based, capture, terminal,
    z, hz, hzy, cap, S.calibration.cap_refinement _ z cap⟩

end PoincareConjecture.Proofs.M47

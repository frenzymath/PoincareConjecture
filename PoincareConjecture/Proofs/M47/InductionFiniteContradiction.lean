import PoincareConjecture.Proofs.M47.LimitFiniteEndpointService
import PoincareConjecture.Proofs.M47.LimitFiniteUniformSlab










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance inductionFiniteTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance inductionFiniteCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance inductionFiniteManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

variable
  (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (baseTime k)
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))
    (F k).parameters.epsilon (F k).parameters.C)
  (capBudget :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    ∀ j : ℕ, ∀ᶠ k in atTop,
    ∀ (C : GeneralizedSliceCarrier.{u}) {Ucap : Set C.carrier}, IsOpen Ucap →
    ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
    ∀ E0 : SurgeryFlowCylinder (F (G.subsequence k)) C (baseTime (G.subsequence k))
        (seq.scale (G.subsequence k)) (Icc a 0) Ucap,
      (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ Ucap,
        ((F (G.subsequence k)).connection
          (baseTime (G.subsequence k) + s / seq.scale (G.subsequence k))).scalarCurvature
            (E0.forward s hs x) ≤ ((j : ℝ) + 1) * seq.scale (G.subsequence k)) →
      let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
      let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
      let tbirth := baseTime (G.subsequence k) + a / seq.scale (G.subsequence k)
      ∀ (hEvent : tbirth ∈ (F (G.subsequence k)).surgery_times),
      ∀ [Nonempty ((F (G.subsequence k)).slice tbirth).carrier],
      ∀ (i : Fin ((F (G.subsequence k)).event tbirth hEvent).cap_count) (contact : C.carrier),
        contact ∈ Ucap →
        E0.forward a bottom contact ∈
          (((F (G.subsequence k)).event tbirth hEvent).caps i).carrier →
        (∀ x ∈ Ucap, ((F (G.subsequence k)).metric tbirth).edist
          (E0.forward a bottom contact) (E0.forward a bottom x) ≤
            ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (seq.scale (G.subsequence k)))) →
        ∀ y ∈ Ucap,
          ((F (G.subsequence k)).connection
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))).scalarCurvature
              (E0.forward 0 zero y) = seq.scale (G.subsequence k) →
          SurgeryCanonicalControl (F (G.subsequence k))
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))
            (E0.forward 0 zero y) (F (G.subsequence k)).parameters.epsilon
            (F (G.subsequence k)).parameters.C)

include hbad capBudget in



theorem induction_exists_finite_horizon_extension
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (controls : M30GeometricLongControls V H)
    (p : ℕ → SurgeryParameterPrefix S.constants) (O : ∀ k, SurgeryObservation (F k))
    (hfinite : H ≠ ⊤)
    (hInitial : ∀ k, (F k).standard_initial = S.setup.standard_initial)
    (hConstants : ∀ k, (F k).local_constants = S.constants)
    (hParameters : ∀ k, (F k).parameters.epsilon = S.setup.epsilon ∧
      (F k).parameters.C = S.setup.C)
    (hBase : ∀ k, baseTime k ∈ Ico (surgeryEpochStart (p k).i) (O k).H)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (hOverlap : ∀ k, ∀ t ∈ surgeryObservationInterval (O k) ∩
        Ico (surgeryEpochStart ((p k).i - 1)) (O k).H,
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants) :
    ∃ rho : ℕ → ℕ, ∃ hrho : StrictMono rho,
      ∃ T : ℝ, 0 < T ∧ H.toReal < T ∧
        TerminalCommonIntervalSlab (terminalCommonInterval_reindex V rho hrho) T := by
  obtain ⟨sigma, hsigma, _gE, _DE, _hcomplete, _hoperator, etaIndex, hetaIndex,
    _hn, psi, _hpsiSource, _htimes, Bglobal, _hBglobal, _hbound, hL, hballs⟩ :=
    limitFinite_actual_endpoint_terminal_ball_service F W history baseTime hbaseTime
      basePoint hPositive hDiverges G hbad capBudget P S B p O controls.horizon_pos hfinite
      hInitial hConstants hParameters hBase hPinched rNext hThreshold hEarlier hOverlap
  obtain ⟨T, hT, hlarge, rho, hrho, _hrho, hslab⟩ :=
    limitFinite_exists_selected_longer_slab F W history baseTime hbaseTime basePoint
      hPositive hDiverges G sigma etaIndex P S B controls hfinite hsigma hetaIndex p O
      hInitial hConstants (fun k => (hParameters k).2) hBase hPinched rNext hThreshold
      hEarlier hOverlap hbad psi (2 * max 1 (3 * Bglobal)) hL hballs
      (fun j => (hsigma.comp hetaIndex).tendsto_atTop.eventually (capBudget j))
  exact ⟨rho, hrho, T, hT, hlarge, hslab⟩

end PoincareConjecture.M47

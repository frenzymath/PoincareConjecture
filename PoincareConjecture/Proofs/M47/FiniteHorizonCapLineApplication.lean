import PoincareConjecture.Proofs.M47.LimitFiniteEndpointService
import PoincareConjecture.Proofs.M47.FiniteHorizonCapLineControls
import PoincareConjecture.Proofs.M47.FiniteHorizonCapLineContradiction

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

private local instance capLineApplicationTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance capLineApplicationCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance capLineApplicationManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
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

theorem finiteHorizon_exists_cap_line_exclusion
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
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ etaIndex : ℕ → ℕ, StrictMono etaIndex ∧
        ∃ d K : ℝ, 0 < d ∧ d ≤ H.toReal / 4 ∧ 0 ≤ K ∧
          let qIndex := fun k => sigma (etaIndex k)
          let index := fun k => G.subsequence (qIndex k)
          let Q := fun k => (V).scale (index k)
          let terminal : ∀ k, G.limit.sliceCarrier.carrier →
              ((F (index k)).slice (baseTime (index k) + 0 / Q k)).carrier := fun k x =>
            (history (index k)).history.forward (baseTime (index k) + 0 / Q k)
              (limitNoncollapse_physical_time_mem G (qIndex k) 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩)
              ((G.embedding (qIndex k)).forward 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩ x)
          let badPoint := fun k => (history (index k)).history.forward
            (baseTime (index k)) (hbaseTime (index k)) (basePoint (index k))
          ∃ hc : -H.toReal < 0,
            (∀ R : ℝ, 0 < R →
              let U := (G.limit.flow.metric 0).ball G.limit.base R
              ∀ᶠ k : ℕ in atTop,
                ∀ (a : ℝ) (_ha : a ∈ Icc (-H.toReal - 4 * d) (-H.toReal)),
                ∀ E : SurgeryFlowCylinder (F (index k)) G.limit.sliceCarrier
                    (baseTime (index k)) (Q k) (Icc a 0) U,
                  (∀ hz : (0 : ℝ) ∈ Icc a 0, ∀ x ∈ U,
                    E.forward 0 hz x = terminal k x) →
                  ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
                    ((F (index k)).connection (baseTime (index k) + s / Q k)).scalarCurvature
                      (E.forward s hs x) ≤ K * Q k) ∧
            ¬ ∃ R : ℝ, 0 < R ∧ ∃ᶠ k : ℕ in atTop,
              FiniteHorizonCapCylinderContact (fun k => F (index k))
                (fun k => baseTime (index k)) Q (G.limit.flow.metric 0) G.limit.base
                terminal badPoint (-H.toReal) d hc k R := by
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  obtain ⟨sigma, hsigma, _gE, _DE, _hcomplete, _hoperator, etaIndex, hetaIndex,
    _hn, psi, _hpsiSource, _htimes, Bglobal, _hBglobal, _hbound, hL, hballs⟩ :=
    limitFinite_actual_endpoint_terminal_ball_service F W history baseTime hbaseTime
      basePoint hPositive hDiverges G hbad capBudget P S B p O controls.horizon_pos hfinite
      hInitial hConstants hParameters hBase hPinched rNext hThreshold hEarlier hOverlap
  let L := 2 * max 1 (3 * Bglobal)
  obtain ⟨d, Bold, hd, hdT, _hshort, _hBold, hline⟩ :=
    finiteHorizon_eventually_cap_line_bound F W history baseTime hbaseTime basePoint
      hPositive hDiverges G sigma etaIndex P S B controls hfinite hsigma hetaIndex p O
      hInitial hConstants (fun k => (hParameters k).2) hBase hPinched rNext hThreshold
      hEarlier hOverlap psi L hL hballs
  let K := max (4 * L) (3 * Bold)
  have hK : 0 ≤ K :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (zero_le_one.trans hL)).trans (le_max_left _ _)
  let qIndex := fun k => sigma (etaIndex k)
  let index := fun k => G.subsequence (qIndex k)
  let Q := fun k => (V).scale (index k)
  let terminal : ∀ k, G.limit.sliceCarrier.carrier →
      ((F (index k)).slice (baseTime (index k) + 0 / Q k)).carrier := fun k x =>
    (history (index k)).history.forward (baseTime (index k) + 0 / Q k)
      (limitNoncollapse_physical_time_mem G (qIndex k) 0
        ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩)
      ((G.embedding (qIndex k)).forward 0
        ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩ x)
  let badPoint := fun k => (history (index k)).history.forward
    (baseTime (index k)) (hbaseTime (index k)) (basePoint (index k))
  have hc : -H.toReal < 0 :=
    neg_neg_of_pos (ENNReal.toReal_pos controls.horizon_pos.ne' hfinite)
  have hindex : StrictMono index := G.subsequence_strictMono.comp (hsigma.comp hetaIndex)
  have hQ : ∀ k, 0 < Q k := fun k => (V).base_scalar_pos (index k)
  have hQdiv : Tendsto Q atTop atTop := (V).scalar_diverges.comp hindex.tendsto_atTop
  have hscalarBad : ∀ k,
      ((F (index k)).connection (baseTime (index k))).scalarCurvature (badPoint k) = Q k :=
    fun k => (history (index k)).scalar_pullback _ _ _
  refine ⟨sigma, hsigma, etaIndex, hetaIndex, d, K, hd, hdT, hK, hc, hline, ?_⟩
  apply finiteHorizon_no_frequent_cap_of_scalar_service (C := G.limit.sliceCarrier)
    (fun k => F (index k)) (fun k => baseTime (index k)) Q (G.limit.flow.metric 0)
    G.limit.base terminal badPoint P hc hK hQ hQdiv
    (fun k => hPinched (index k)) hscalarBad (fun k => hbad (index k)) hline
  intro j R _hR
  have hU : IsOpen ((G.limit.flow.metric 0).ball G.limit.base R) :=
    M04.initial_ball_isOpen _ _ _
  filter_upwards [(hsigma.comp hetaIndex).tendsto_atTop.eventually (capBudget j)] with k hk
  intro a ha E hscalar hEvent inst i contact hcontact hcap hdist y hy hnorm
  exact @hk G.limit.sliceCarrier _ hU a ha E hscalar hEvent inst i contact hcontact hcap
    hdist y hy hnorm

end PoincareConjecture.M47

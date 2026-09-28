import PoincareConjecture.Proofs.M47.LimitFiniteEndpointRows
import PoincareConjecture.Proofs.M47.LimitFiniteActualExtraction
import PoincareConjecture.Proofs.M47.LimitFiniteActualGerms
import PoincareConjecture.Proofs.M47.LimitFiniteActualMetric
import PoincareConjecture.Proofs.M47.LimitFiniteRetainedService










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance endpointServiceDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointServiceDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance endpointServiceBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointServiceBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace

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

private local instance endpointServiceTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance endpointServiceCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance endpointServiceManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance endpointServiceMeasurable : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance endpointServiceBorel : BorelSpace G.limit.carrier.carrier :=
  G.limit.carrier.borelSpace
private local instance endpointServiceT2 : T2Space G.limit.carrier.carrier :=
  G.limit.carrier.t2Space
private local instance endpointServiceT3 : T3Space G.limit.carrier.carrier :=
  G.limit.carrier.t3Space
private local instance endpointServiceSecondCountable :
    SecondCountableTopology G.limit.carrier.carrier := G.limit.carrier.secondCountable
private local instance endpointServiceConnected : ConnectedSpace G.limit.carrier.carrier :=
  G.limit.connectedSpace

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))

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



theorem limitFinite_actual_endpoint_terminal_ball_service
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : ℕ → SurgeryParameterPrefix S.constants) (O : ∀ k, SurgeryObservation (F k))
    (hH : 0 < H) (hfinite : H ≠ ⊤)
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
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier, ∃ DE : LeviCivitaData gE,
        MetricComplete gE ∧ (∀ x, DE.NonnegativeCurvatureOperator x) ∧
        ∃ η : ℕ → ℕ, StrictMono η ∧ StrictMono (fun k => G.subsequence (σ (η k))) ∧
          ∃ ψ : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
              ((F (G.subsequence (σ (η k)))).slice
                (baseTime (G.subsequence (σ (η k))) +
                  -H.toReal / (V).scale (G.subsequence (σ (η k))))).carrier ∞,
            (∀ k, (ψ k).source = G.exhaustion.space k) ∧
            (∀ k, 0 < (V).scale (G.subsequence (σ (η k))) ∧
              baseTime (G.subsequence (σ (η k))) +
                -H.toReal / (V).scale (G.subsequence (σ (η k))) ∈
                  (F (G.subsequence (σ (η k)))).time_domain ∧
              baseTime (G.subsequence (σ (η k))) +
                -H.toReal / (V).scale (G.subsequence (σ (η k))) ∈
                  Ico 0 (baseTime (G.subsequence (σ (η k))))) ∧
            ∃ Bglobal : ℝ, 0 < Bglobal ∧ (∀ x, DE.curvatureTensorNorm x ≤ Bglobal) ∧
            let Lscalar := 2 * max 1 (3 * Bglobal)
            1 ≤ Lscalar ∧ ∀ radius : ℝ, 0 < radius →
              let Uball := (G.limit.flow.metric 0).ball G.limit.base radius
              ∀ᶠ k : ℕ in atTop, Uball ⊆ G.exhaustion.space (σ (η k)) ∧
                ∃ e0 : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
                    (baseTime (G.subsequence (σ (η k)))) ((V).scale (G.subsequence (σ (η k))))
                    (Icc (-H.toReal) 0) Uball,
                  EqOn (ψ k) (e0.forward (-H.toReal)
                    ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩) Uball ∧
                  (∀ s (hs : s ∈ Icc (-H.toReal) 0)
                    (hsG : s ∈ Icc (-G.exhaustion.time (σ (η k))) 0), ∀ x ∈ Uball,
                    e0.forward s hs x = (history (G.subsequence (σ (η k)))).history.forward
                      (baseTime (G.subsequence (σ (η k))) +
                        s / (V).scale (G.subsequence (σ (η k))))
                      (limitNoncollapse_physical_time_mem G (σ (η k)) s hsG)
                      ((G.embedding (σ (η k))).forward s hsG x)) ∧
                  (∀ s (hs : s ∈ Icc (-H.toReal) 0)
                    (hsG : s ∈ Icc (-G.exhaustion.time (σ (η k))) 0), ∀ x ∈ Uball,
                    ∀ v w : TangentSpace (𝓡 3) x,
                      e0.pullbackInner s hs x v w =
                        (G.embedding (σ (η k))).pullbackInner s hsG x v w) ∧
                  (∀ x ∈ Uball,
                    ((F (G.subsequence (σ (η k)))).connection
                      (baseTime (G.subsequence (σ (η k))) +
                        -H.toReal / (V).scale (G.subsequence (σ (η k))))).scalarCurvature
                      (e0.forward (-H.toReal)
                        ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩ x) ≤
                          Lscalar * (V).scale (G.subsequence (σ (η k)))) ∧
                  (∀ x ∈ Uball, ∀ v : TangentSpace (𝓡 3) x,
                    e0.pullbackInner 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ x v v ≤
                      2 * (G.limit.flow.metric 0).inner x v v) ∧
                  ((⟨baseTime (G.subsequence (σ (η k))) +
                      0 / (V).scale (G.subsequence (σ (η k))),
                      e0.forward 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ G.limit.base⟩ :
                      Σ t, ((F (G.subsequence (σ (η k)))).slice t).carrier) =
                    ⟨baseTime (G.subsequence (σ (η k))),
                      (history (G.subsequence (σ (η k)))).history.forward
                        (baseTime (G.subsequence (σ (η k))))
                        (hbaseTime (G.subsequence (σ (η k))))
                        (basePoint (G.subsequence (σ (η k))))⟩) := by
  classical
  obtain ⟨d, K, hd, hK, hc, A, hactual⟩ := limitFinite_actual_endpoint_rows F W history
    baseTime hbaseTime basePoint hPositive hDiverges G hbad capBudget P S B p O hH hfinite
    hInitial hConstants hParameters hBase hPinched rNext hThreshold hEarlier hOverlap
  have hcandidates : ∀ j, ∀ᶠ k : ℕ in atTop,
      (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U j,
        |((A j k).connection s).curvatureTensorNorm x| ≤ K j) ∧
      ∃ ht : -H.toReal + d j / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ (x : U j) (v w : TangentSpace (𝓡 3) x),
          ((A j k).metric (-H.toReal + d j / 4)).inner x v w =
            (G.embedding k).pullbackInner (-H.toReal + d j / 4) ht x.val
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w) := by
    intro j
    filter_upwards [hactual j] with k hk
    obtain ⟨hI, _hspace, b, _hb, e, _hmap, _hnorm, hAnorm, _hmetric, hold⟩ := hk
    have ha : -H.toReal + d j / 4 ∈ Icc (-(H.toReal + d j / 2)) 0 :=
      ⟨by linarith only [hd j], (hc j).1⟩
    exact ⟨hAnorm, hI ⟨le_rfl, (hc j).1⟩,
      fun x v w => hold _ ha _ x v w⟩
  obtain ⟨j, hj, N, _centers, R, ρ, Φ, hdata, hcover, _hcharts,
    σ, hσ, coeff, hcoeffSmooth, hjets, hpoint, hsymm, hquad⟩ :=
    limitFinite_actual_endpoint_extraction G P d K hd hK hc A hcandidates
  have hρ : ∀ m i, 0 < ρ m i := fun m i => (hdata m i).1
  have hρR : ∀ m i, ρ m i < R m i := by
    intro m i
    linarith only [hρ m i, (hdata m i).2.1]
  have hsource : ∀ m i, (Φ m i).source = Metric.ball 0 (R m i) :=
    fun m i => (hdata m i).2.2.1
  have hlower : ∀ m i, ∃ a : ℝ, 0 < a ∧
      ∀ z ∈ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ m i),
        ∀ v : E, a * ‖v‖ ^ 2 ≤ coeff m i z v v := by
    intro m i
    obtain ⟨a, b, ha, _hb, hab⟩ := hquad m i
    exact ⟨a, ha, fun z hz v => (hab z hz v).1⟩
  let Wb := fun z : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ z.1 z.2)
  let hWb : ∀ z, IsOpen (Wb z) := fun _ => Metric.isOpen_ball
  let : ∀ z, Nonempty (Piece Wb z) :=
    fun z => ⟨⟨0, Metric.mem_ball_self (hρ z.1 z.2)⟩⟩
  let : ∀ z, ChartedSpace E (Piece Wb z) :=
    fun z => (hWb z).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ z, IsManifold (𝓡 3) ∞ (Piece Wb z) :=
    fun z => (hWb z).isOpenEmbedding_subtypeVal.isManifold_singleton
  obtain ⟨Fc, Ag, _hcenter, hcoeff, hread, hold, hcompat⟩ :=
    limitFinite_actual_endpoint_germs F W history baseTime hbaseTime basePoint hPositive
      hDiverges G d K hd hc A hactual j N R ρ hρ hρR Φ hsource hcover σ hσ coeff
      hcoeffSmooth hjets hpoint hsymm hlower
  obtain ⟨gE, DE, hcomplete, _hfloor, hoperator, _hterminalSlots, _hterminalFlat,
    hinner, hconnected, htriple, L, _hdL, _hLclock, hLmetric, hLoperator⟩ :=
    limitFinite_actual_endpoint_metric F W history baseTime hbaseTime basePoint hPositive
      hDiverges G P hfinite hPinched d K hd (fun m => (hK m).le) hc A hactual
      j N R ρ hρ hρR Φ hsource hcover σ hσ coeff hcoeffSmooth hjets
      Fc hcoeff Ag hread hold hcompat
  refine ⟨σ, hσ, gE, DE, hcomplete, hoperator, ?_⟩
  exact limitFinite_actual_retained_terminal_ball_service F W history baseTime hbaseTime
    basePoint hPositive hDiverges G P S rNext hThreshold (fun k => (hParameters k).1)
    (fun k => (hParameters k).2) hEarlier hfinite d K hd hc A hactual
    j N hj R ρ hρR Φ hsource hcover σ hσ coeff hcoeffSmooth hjets gE DE hcomplete
    hoperator hinner hconnected L hLmetric hLoperator htriple

end PoincareConjecture.M47

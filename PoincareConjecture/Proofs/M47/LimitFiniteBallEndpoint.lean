import PoincareConjecture.Proofs.M47.LimitFiniteOpenEndpoint
import PoincareConjecture.Proofs.M47.LimitCapSourceDistance
import PoincareConjecture.Proofs.M47.LimitNoncollapseSourceCenters









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

private local instance ballEndpointTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance ballEndpointCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance ballEndpointManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold



theorem limitFinite_eventually_preserved_ball_endpoint_search
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
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (R : ℝ) (hR : 0 < R) :
    let U := (G.limit.flow.metric 0).ball G.limit.base R
    ∃ d L D : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ 1 ≤ L ∧ 0 < D ∧
      let c := -H.toReal + d / 4
      ∃ hc : c ∈ blowupBackwardInterval H, c < 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0,
          U ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) (U),
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ U,
                  E.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
                  E.pullbackInner s hs' x v w =
                    (G.embedding k).pullbackInner s (hI hs) x v w) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).scalarCurvature
                    (E.forward s hs x) ≤ 4 * L * (V).scale (G.subsequence k) ∧
                |((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).curvatureTensorNorm
                    (E.forward s hs x)| ≤ (13 * max (4 * L) 1) * (V).scale (G.subsequence k) ∧
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).negativeCurvaturePart
                    (E.forward s hs x) ≤ eta * (V).scale (G.subsequence k)) ∧
              (∀ contact ∈ U, ∀ x ∈ U,
                ((F (G.subsequence k)).metric
                  (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).edist
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ contact)
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ x) ≤
                    ENNReal.ofReal (D / Real.sqrt ((V).scale (G.subsequence k)))) ∧
              (b < -H.toReal - d / 2 ∨ b ∈ Icc (c - d) c ∧
                ∃ hEvent : baseTime (G.subsequence k) + b / (V).scale (G.subsequence k) ∈
                    (F (G.subsequence k)).surgery_times,
                  ∀ [Nonempty ((F (G.subsequence k)).slice
                      (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).carrier],
                    ∃ i : Fin ((F (G.subsequence k)).event
                      (baseTime (G.subsequence k) +
                        b / (V).scale (G.subsequence k)) hEvent).cap_count,
                      Set.Nonempty (E.forward b ⟨le_rfl, hb.2.trans (by
                        exact hc.1)⟩ ''
                          U ∩
                        (((F (G.subsequence k)).event
                          (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))
                            hEvent).caps i).carrier)) := by
  intro U
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let g := G.limit.flow.metric 0
  have hU : IsOpen U := M04.initial_ball_isOpen g G.limit.base R
  have hUcompact : IsCompact (closure U) :=
    Proofs.M09.isCompact_closure_metric_ball g (G.limit.complete 0 G.limit.zero_mem)
      G.limit.base R
  have hbaseU : G.limit.base ∈ U := by
    change g.edist G.limit.base G.limit.base < ENNReal.ofReal R
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hR
  obtain ⟨d, L, hd, hdsmall, hL, hc, hcneg, search⟩ :=
    limitFinite_eventually_preserved_open_endpoint_search F W history baseTime hbaseTime
      basePoint hPositive hDiverges G P S B p O hH hfinite hInitial hConstants hParameters
      hBase hPinched rNext hThreshold hEarlier hOverlap hterminal U hU hUcompact
        ⟨G.limit.base, hbaseU⟩
  let c := -H.toReal + d / 4
  let K := 13 * max (4 * L) 1
  let T := H.toReal + 1
  let D := 2 * Real.sqrt (2 * Real.exp (6 * K * T)) * R
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨d, L, D, hd, hdsmall, hL, hD, hc, hcneg, ?_⟩
  intro eta heta
  filter_upwards [search eta heta, limitNoncollapse_compact_inner_zero G hUcompact]
    with k hk hzero
  obtain ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, hstop⟩ := hk
  refine ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, ?_, hstop⟩
  have hage : b ∈ Icc (-T) 0 := by
    refine ⟨?_, hb.2.trans hc.1⟩
    change -(H.toReal + 1) ≤ b
    have hlo : -H.toReal + d / 4 - 2 * d ≤ b := hb.1
    linarith only [hlo, hdsmall]
  have hRm (s : ℝ) (hs : s ∈ Icc b 0) (x : G.limit.carrier.carrier) (hx : x ∈ U) :
      ((F (G.subsequence k)).connection
        (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
          (E.forward s hs x) ≤ K * (V).scale (G.subsequence k) :=
    (le_abs_self _).trans (hbounds s hs x hx).2.1
  have hterminalE (x : G.limit.carrier.carrier) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      E.pullbackInner 0 ⟨hage.2, le_rfl⟩ x v v ≤ 2 * g.inner x v v := by
    rw [hmetric 0 ⟨hcneg.le, le_rfl⟩ ⟨hage.2, le_rfl⟩ x hx v v]
    exact (hzero.2 x (subset_closure hx) v).2
  exact finite_source_ball_bottom_distance (F := F (G.subsequence k))
    (C := G.limit.sliceCarrier) ⟨P.m04, P.m13.ordinary_flow⟩
    (hPinched (G.subsequence k)) g G.limit.base hR hK hage E hRm hterminalE

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M47.LimitFinitePreservedEndpoint
import PoincareConjecture.Proofs.M47.LimitFiniteInteriorFlow









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

private local instance sourceAlternativeTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance sourceAlternativeCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance sourceAlternativeManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold



theorem limitFinite_eventually_source_alternative
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
    (j : ℕ) :
    ∃ d L : ℝ, 0 < d ∧ 1 ≤ L ∧
      let c := -H.toReal + d / 4
      let tau := H.toReal + d / 2
      let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
        ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
      ∃ hc : c ∈ blowupBackwardInterval H,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0,
          G.exhaustion.space j ⊆ G.exhaustion.space k ∧
          ((∃ A : RicciFlow 3 U (Icc (-tau) 0),
            (∀ s ∈ Icc (-tau) 0, ∀ x : U,
              |(A.connection s).curvatureTensorNorm x| ≤ 13 * max (4 * L) 1) ∧
            (∀ s (hs : s ∈ Icc c 0) (x : U), ∀ v w : TangentSpace (𝓡 3) x,
              (A.metric s).inner x v w = (G.embedding k).pullbackInner s (hI hs) x.val
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.carrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.carrier.carrier) x w))) ∨
          ∃ (b : ℝ) (hb : b ∈ Icc (c - d) c),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) (G.exhaustion.space j),
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j,
                  E.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j, ∀ v w : TangentSpace (𝓡 3) x,
                  E.pullbackInner s hs' x v w =
                    (G.embedding k).pullbackInner s (hI hs) x v w) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
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
              ∃ hEvent : baseTime (G.subsequence k) + b / (V).scale (G.subsequence k) ∈
                  (F (G.subsequence k)).surgery_times,
                ∀ [Nonempty ((F (G.subsequence k)).slice
                    (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).carrier],
                  ∃ i : Fin ((F (G.subsequence k)).event
                    (baseTime (G.subsequence k) +
                      b / (V).scale (G.subsequence k)) hEvent).cap_count,
                    Set.Nonempty (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ ''
                      G.exhaustion.space j ∩
                      (((F (G.subsequence k)).event
                        (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))
                          hEvent).caps i).carrier)) := by
  obtain ⟨d, L, hd, hL, hc, hsearch⟩ :=
    limitFinite_eventually_preserved_endpoint_search F W history baseTime hbaseTime
      basePoint hPositive hDiverges G P S B p O hH hfinite hInitial hConstants
      hParameters hBase hPinched rNext hThreshold hEarlier hOverlap hterminal j
  let c := -H.toReal + d / 4
  let tau := H.toReal + d / 2
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  have htau : 0 < tau := by
    dsimp only [tau]
    linarith [ENNReal.toReal_nonneg (a := H)]
  have hctau : -tau ≤ c := by dsimp only [tau, c]; linarith
  refine ⟨d, L, hd, hL, hc, ?_⟩
  intro eta heta
  filter_upwards [hsearch eta heta] with k hk
  obtain ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, hstop⟩ := hk
  refine ⟨hI, hspace, ?_⟩
  rcases hstop with hlong | hcap
  · have hb' : b < -tau := by dsimp only [tau]; linarith only [hlong]
    let e0 : GeneralizedFlowCylinder (history (G.subsequence k)).generalized
        G.limit.sliceCarrier (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
        (Icc c 0) (U : Set G.limit.sliceCarrier.carrier) := (G.embedding k).restrict hI hspace
    obtain ⟨A, _hread, hcurv, hfuture⟩ := limitFinite_preserved_interior_flow
      P (history (G.subsequence k)) (C := G.limit.sliceCarrier)
      (Q := (V).scale (G.subsequence k)) (c := c)
      U ⟨G.limit.base, G.exhaustion.base_mem j⟩
      (hbaseTime (G.subsequence k)) htau hb' E e0
      (fun s hs hs' x hx => hmap s hs hs' x hx)
      (fun s hs x hx => (hbounds s hs x hx).2.1)
    refine Or.inl ⟨A, hcurv, ?_⟩
    intro s hs x v w
    exact hfuture s hs ⟨hctau.trans hs.1, hs.2⟩ x v w
  · exact Or.inr ⟨b, hcap.1, E, hmap, hmetric, hbounds, hcap.2⟩

end PoincareConjecture.M47

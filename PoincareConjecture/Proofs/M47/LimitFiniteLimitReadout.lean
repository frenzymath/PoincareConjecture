import PoincareConjecture.Proofs.M47.LimitFiniteSliceJets
import PoincareConjecture.Proofs.M47.LimitFiniteSliceCanonical
import PoincareConjecture.Proofs.M47.LimitFiniteSourceReadout










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

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

private local instance finiteReadoutTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance finiteReadoutCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance finiteReadoutManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold





theorem limitFinite_nearby_neck_of_retained_convergence
    (P : M47Predecessors.{u}) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (htneg : t < 0)
    (x : G.limit.sliceCarrier.carrier)
    (hx : 1 < (G.limit.flow.connection t).scalarCurvature x) :
    (∃ N : EpsilonNeck (G.limit.flow.metric t),
      N.connection = G.limit.flow.connection t ∧ N.epsilon = 2 * epsilon ∧
      (G.limit.flow.connection t).scalarCurvature x ≤
        (4 * max 1 C) * (G.limit.flow.connection t).scalarCurvature N.center ∧
      (G.limit.flow.metric t).edist x N.center < ENNReal.ofReal
        (4 * C * (G.limit.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) ∨
      IsCompact (univ : Set G.limit.carrier.carrier) := by
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let R := fun i => (history i).history
  let phi := limitFinitePhysicalSliceChart G F R t
  let c := fun q : G.limit.sliceCarrier.carrier => limitCanonicalNativeChart q
  have hsource : ∀ k, (phi k).source = G.exhaustion.space k :=
    limitFinite_physical_slice_chart_source G F R t
  have hcoverC : ∀ q : G.limit.sliceCarrier.carrier, ∃ i, q ∈ (c i).source :=
    fun q => ⟨q, mem_extChartAt_source q⟩
  have hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((rescaledMetric ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
          ((V).scale (G.subsequence k))
          ((V).base_scalar_pos (G.subsequence k))).pullbackCoefficients
            (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m ((G.limit.flow.metric t).pullbackCoefficients (c i).symm)) atTop K :=
    fun i m _ hK hKc => limitFinite_physical_slice_coefficient_jets G P F R t ht i m hK hKc
  have hballs (a : ℝ) (ha : 0 < a) : ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
        ((V).scale (G.subsequence k)) ((V).base_scalar_pos (G.subsequence k))).ball
        (phi k x) a ⊆ phi k '' G.exhaustion.space j :=
    terminalCurvature_source_balls_of_original_jets
      (fun k => rescaledMetric ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
        ((V).scale (G.subsequence k)) ((V).base_scalar_pos (G.subsequence k)))
      (G.limit.flow.metric t) (G.limit.complete t ht) G.exhaustion.space
      G.exhaustion.space_open G.exhaustion.space_increasing G.exhaustion.space_covers
      phi hsource c hcoverC (fun i K hK hKc => hjet i 0 K hK hKc) x ha
  have hcanonical := limitFinite_eventually_physical_slice_canonical F W history
    baseTime hbaseTime basePoint hPositive hDiverges G P hfinite hParameters
    rNext hThreshold hEarlier t ht htneg x hx
  exact limitFinite_nearby_neck_of_surgery_source_canonical
    (fun k => F (G.subsequence k)) (limitFinitePhysicalSliceTime G t)
    (fun k => (V).scale (G.subsequence k)) (fun k => (V).base_scalar_pos (G.subsequence k))
    (G.limit.flow.metric t) (G.limit.flow.connection t) G.exhaustion.space
    G.exhaustion.space_open G.exhaustion.space_increasing G.exhaustion.space_covers
    G.exhaustion.space_compactClosure G.limit.base G.exhaustion.base_mem
    phi hsource c hcoverC hjet x (lt_trans zero_lt_one hx) hballs
    hepsilon hsmall hroundSmall hC hcanonical

end PoincareConjecture.M47

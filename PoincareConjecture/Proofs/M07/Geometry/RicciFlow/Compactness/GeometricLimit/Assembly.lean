import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.QuotientMetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.QuotientJetConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Subsequence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

noncomputable def pointedGeometricConvergence_of_quotient_limit
    {ι : Type} [Countable ι] {n : ℕ} {T' T : ℝ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    (hclosed : ∀ i j, IsClosed {q : Piece U i × Piece U j |
      O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})
    [ConnectedSpace (Quotient O.setoid)]
    {D : ℕ → FlowCarrier n}
    (G : ∀ k, BasedFlow n T' T (D k))
    (F : BasedFlow n T' T (O.flowCarrier U hU hO hclosed))
    (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t))
    (hF : let C := O.flowCarrier U hU hO hclosed
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      F.flow.metric = fun t => quotientMetric U hU O hO (gLimit t) (hcompat t))
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEconnected : ∀ k, IsConnected (E k))
    (hEcompact : ∀ k, IsCompact (closure (E k)))
    (hEmono : Monotone E) (hEcover : (⋃ k, E k) = Set.univ)
    (f : ∀ k, Quotient O.setoid → (D k).carrier)
    (hemb : ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier := (D k).chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    (hbase : ∀ k, F.base ∈ E k)
    (hbase_preserving : ∀ k, f k F.base = (G k).base)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBcont : ∀ i, ContinuousOn (B i) (Set.Ioo T' T ×ˢ U i))
    (hB : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ Set.Ioo T' T, ∀ i (x : Piece U i) v w,
        (gLimit t i).inner x v w = B i (t, x) v w)
    (hjets : letI : ∀ k, TopologicalSpace (D k).carrier :=
        fun k => (D k).topologicalSpace
      letI : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
        fun k => (D k).chartedSpace
      letI : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
      ∀ i m K, IsCompact K → K ⊆ Set.Ioo T' T ×ˢ U i →
        TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((G k).flow.metric z.1).pullbackCoefficients
                (chartParametrization U hU (f k ∘ O.include i)) z.2))
          (iteratedFDeriv ℝ m (B i)) atTop K) :
    PointedGeometricConvergence { carrier := D, flow := G } := by
  let C := O.flowCarrier U hU hO hclosed
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T2Space (Quotient O.setoid) := O.quotient_t2Space hclosed
  letI : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
  letI : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
    fun k => (D k).chartedSpace
  letI : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
  have hconv : ∀ i K, IsCompact K → K ⊆ Set.Ioo T' T ×ˢ U i →
      TendstoUniformlyOn
        (fun k p => ((G k).flow.metric p.1).pullbackCoefficients
          (chartParametrization U hU (f k ∘ O.include i)) p.2) (B i) atTop K := by
    intro i K hK hKU
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (hjets i 0 K hK hKU)
  have hpull := pullback_metric_converges_of_quotient_coefficients
    U hU O hO hclosed F G gLimit hcompat hF hE hEmono hEcover f hemb hf
    hBcont (fun i t ht => hB t ht i) hconv
  have hjets' := pullback_metric_CInfinity_of_quotient_coefficient_jets
    U hU O hO hclosed F G gLimit hcompat hF B hB E hE hEmono f hemb hf hjets
  refine
    { limitCarrier := C
      limitFlow := F
      subsequence := fun k => k
      subsequence_strictMono := strictMono_id
      exhaustion := E
      exhaustion_open := hE
      exhaustion_connected := hEconnected
      exhaustion_compactClosure := hEcompact
      exhaustion_increasing := fun j => hEmono (Nat.le_succ j)
      exhaustion_covers := hEcover
      embedding := fun k => SmoothSpacetimeEmbedding.of_spatial F (G k)
        (hE k) (f k) (hemb k) (hf k) (Set.Ioo T' T)
      base_in_exhaustion := hbase
      base_preserving := ?_
      pullback_metric_converges := hpull
      pullback_metric_CInfinity := hjets' }
  intro k
  exact congrArg (fun x => (0, x)) (hbase_preserving k)

end PoincareConjecture.ChartDistance

namespace PoincareConjecture





noncomputable def PointedGeometricConvergence.reindex
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : PointedGeometricConvergence
      { carrier := fun k => S.carrier (φ k)
        flow := fun k => S.flow (φ k) }) :
    PointedGeometricConvergence S :=
  G.ofSubsequence hφ

end PoincareConjecture

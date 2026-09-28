import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Pointed













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {n : ℕ} (D : ℕ → FlowCarrier.{0} n)

local instance ancientAssembly_sourceTopology (k : ℕ) :
    TopologicalSpace (D k).carrier := (D k).topologicalSpace
local instance ancientAssembly_sourceCharts (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
  (D k).chartedSpace
local instance ancientAssembly_sourceManifold (k : ℕ) :
    IsManifold (𝓡 n) ∞ (D k).carrier := (D k).isManifold




noncomputable def completeAncientConvergence
    {ι : Type} [Countable ι]
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    (hclosed : ∀ i j, IsClosed {q : Piece U i × Piece U j |
      O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})
    [ConnectedSpace (Quotient O.setoid)]
    {T : ℝ} (hT : 0 < T)
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (D k).carrier (J k))
    (p : ∀ k, (D k).carrier)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (F : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      RicciFlow n (Quotient O.setoid) (Iio T))
    (q : Quotient O.setoid)
    (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t))
    (hF : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      F.metric = fun t => quotientMetric U hU O hO (gLimit t) (hcompat t))
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEc : ∀ k, IsConnected (E k))
    (hEK : ∀ k, IsCompact (closure (E k)))
    (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    (f : ∀ k, Quotient O.setoid → (D k).carrier)
    (hemb : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    (hbase : ∀ k, q ∈ E k) (hbase_preserving : ∀ k, f k q = p k)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBcont : ∀ i, ContinuousOn (B i) (Iio T ×ˢ U i))
    (hB : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ Iio T, ∀ i (x : Piece U i) v w,
        (gLimit t i).inner x v w = B i (t, x) v w)
    (hjets : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (f k ∘ O.include i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤
        ((D k).metricEMetricSpace ((Fseq k).metric 0)).edist (p k) (f k x)) :
    {G : AncientPointedGeometricConvergence D (fun k ↦ (Fseq k).metric) p T //
      letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      G.limitCarrier.metricComplete (G.limitFlow.metric 0)} := by
  classical
  let C := O.flowCarrier U hU hO hclosed
  letI := quotientChartedSpace U hU O
  letI := quotient_isManifold U hU O hO
  let window (a b : ℝ) (hw : a < 0 ∧ 0 < b) (hb : b ≤ T)
      (N : ℕ) (hsub : ∀ k, Ioo a b ⊆ J (k + N)) :=
    completeAncientWindowConvergence D U hU O hO hclosed hw hb Fseq p N hsub
      F q gLimit hcompat hF hE hEc hEK hEmono hEcover f hemb hf hbase
      hbase_preserving B hBcont hB hjets hescape
  refine ⟨{
    limitCarrier := C
    limitFlow := F
    base := q
    subsequence := id
    subsequence_strictMono := strictMono_id
    exhaustion := E
    exhaustion_open := hE
    exhaustion_connected := hEc
    exhaustion_compactClosure := hEK
    exhaustion_increasing := fun j ↦ hEmono (Nat.le_succ j)
    exhaustion_covers := hEcover
    embedding := f
    embedding_open := hemb
    embedding_smooth := hf
    base_in_exhaustion := hbase
    base_preserving := hbase_preserving
    pullback_metric_converges := ?_
    pullback_metric_CInfinity := ?_ }, ?_⟩
  · intro j K I hK hKj hI hIT ε hε
    obtain ⟨a, b, ha, hb0, hbT, hIab⟩ := exists_ancient_window_of_isCompact hT hI hIT
    obtain ⟨N, hsub⟩ := exists_source_window_tail (htime a b hbT)
    let W := window a b ⟨ha, hb0⟩ hbT.le N hsub
    obtain ⟨M, hjM, hM⟩ := W.val.pullback_metric_converges j K I hK hKj hI hIab ε hε
    refine ⟨M + N, by omega, ?_⟩
    intro k hk t ht x hx v w hv hw
    have hidx : k - N + N = k := Nat.sub_add_cancel (by omega)
    have hh := hM (k - N) (by omega) t ht x hx v w hv hw
    change |spatialPullbackInner C (D (k - N + N)) ((Fseq (k - N + N)).metric t)
        (f (k - N + N)) x v w - C.metricInner (F.metric t) x v w| < ε at hh
    exact hidx ▸ hh
  · intro q' j r K hK hKJ ε hε
    have hKT : Prod.fst '' K ⊆ Iio T := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hKJ hz).1
    obtain ⟨a, b, ha, hb0, hbT, hKab⟩ := exists_ancient_window_of_isCompact hT
      (hK.image continuous_fst) hKT
    obtain ⟨N, hsub⟩ := exists_source_window_tail (htime a b hbT)
    let W := window a b ⟨ha, hb0⟩ hbT.le N hsub
    obtain ⟨M, hjM, hM⟩ := W.val.pullback_metric_CInfinity q' j r K hK
      (fun z hz ↦ ⟨hKab (mem_image_of_mem _ hz), (hKJ hz).2⟩) ε hε
    refine ⟨M + N, by omega, ?_⟩
    intro k hk i l z hz
    have hidx : k - N + N = k := Nat.sub_add_cancel (by omega)
    have hh := hM (k - N) (by omega) i l z hz
    change ‖MetricJet r (C.coordinateCoefficient q'
        (fun t x v w ↦ spatialPullbackInner C (D (k - N + N))
          ((Fseq (k - N + N)).metric t) (f (k - N + N)) x v w) i l) K z -
        MetricJet r (C.coordinateCoefficient q'
          (fun t x v w ↦ C.metricInner (F.metric t) x v w) i l) K z‖ < ε at hh
    exact hidx ▸ hh
  · obtain ⟨N, hsub⟩ := exists_source_window_tail (htime (-1) (T / 2) (by linarith))
    exact (window (-1) (T / 2) ⟨by norm_num, by linarith⟩ (by linarith) N hsub).property

end PoincareConjecture.ChartDistance

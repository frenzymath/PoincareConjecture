import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.UniformMetric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SpacetimeEmbedding









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

theorem pullback_metric_converges_of_quotient_coefficients
    {ι : Type*} [Countable ι] {n : ℕ} {T' T : ℝ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    (hclosed : ∀ i j, IsClosed {q : Piece U i × Piece U j |
      O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩}) [ConnectedSpace (Quotient O.setoid)]
    (F : BasedFlow n T' T (O.flowCarrier U hU hO hclosed))
    {D : ℕ → FlowCarrier n} (G : ∀ k, BasedFlow n T' T (D k))
    (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t))
    (hF : let C := O.flowCarrier U hU hO hclosed
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      F.flow.metric = fun t => quotientMetric U hU O hO (gLimit t) (hcompat t))
    {E : ℕ → Set (Quotient O.setoid)} (hE : ∀ k, IsOpen (E k))
    (hEmono : Monotone E) (hEcover : (⋃ k, E k) = Set.univ)
    [T2Space (Quotient O.setoid)]
    (f : ∀ k, Quotient O.setoid → (D k).carrier)
    (hemb : ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier := (D k).chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    {B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hB : ∀ i, ContinuousOn (B i) (Ioo T' T ×ˢ U i))
    (hcoeff : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i t, t ∈ Ioo T' T → ∀ (x : Piece U i) v w,
        (gLimit t i).inner x v w = B i (t, x) v w)
    (hconv : letI : ∀ k, TopologicalSpace (D k).carrier :=
        fun k => (D k).topologicalSpace
      letI : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
        fun k => (D k).chartedSpace
      letI : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier :=
        fun k => (D k).isManifold
      ∀ i C, IsCompact C → C ⊆ Ioo T' T ×ˢ U i →
      TendstoUniformlyOn
        (fun k p => ((G k).flow.metric p.1).pullbackCoefficients
          (chartParametrization U hU (f k ∘ O.include i)) p.2)
        (B i) atTop C) :
    let C := O.flowCarrier U hU hO hclosed
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    ∀ (j : ℕ) (K : Set (Quotient O.setoid)) (I : Set ℝ),
      IsCompact K → K ⊆ E j → IsCompact I → I ⊆ Ioo T' T →
      ∀ ε > 0, ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ t ∈ I, ∀ x ∈ K, ∀ v w : C.tangent x,
          C.metricNorm (F.flow.metric t) x v ≤ 1 →
          C.metricNorm (F.flow.metric t) x w ≤ 1 →
          |pullbackInnerValue F (G k)
              (SmoothSpacetimeEmbedding.of_spatial F (G k) (hE k) (f k)
                (hemb k) (hf k) (Ioo T' T)) t x v w -
            C.metricInner (F.flow.metric t) x v w| < ε := by
  let C := O.flowCarrier U hU hO hclosed
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient O.setoid) :=
    quotientChartedSpace U hU O
  let : IsManifold (𝓡 n) ∞ (Quotient O.setoid) :=
    quotient_isManifold U hU O hO
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨(F.flow.metric 0).toRiemannianMetric⟩
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
    fun k => (D k).chartedSpace
  let : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
  refine fun (j : ℕ) (Kq : Set (Quotient O.setoid)) (Iq : Set ℝ)
    hK hKj hI hIJ ε hε => ?_
  have hbase := source_exhaustion_uniform_metric_error U hU O hO hE hEmono hEcover
    (F := fun k => f k) (hF := hf) (gSource := fun k => (G k).flow.metric)
    (g := fun i t => gLimit t i) (hg := hcompat) (J := Ioo T' T) B
    hB hcoeff (by
      intro i C hC hCJ
      exact hconv i C hC hCJ)
    (K := Kq) (I := Iq) hK hI hIJ ε hε
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hbase)
  refine ⟨max j N, Nat.le_max_left j N, ?_⟩
  intro k hk t ht x hx v w hv hw
  have hkN : N ≤ k := le_trans (le_max_right j N) hk
  have hmetric : C.metricInner (F.flow.metric t) x v w =
      (quotientMetric U hU O hO (fun i => gLimit t i) (hcompat t)).inner x v w := by
    rw [hF]
    rfl
  have hnormv : Real.sqrt
      ((quotientMetric U hU O hO (fun i => gLimit t i) (hcompat t)).inner x v v) ≤ 1 := by
    simpa [FlowCarrier.metricNorm, FlowCarrier.metricInner, hF] using hv
  have hnormw : Real.sqrt
      ((quotientMetric U hU O hO (fun i => gLimit t i) (hcompat t)).inner x w w) ≤ 1 := by
    simpa [FlowCarrier.metricNorm, FlowCarrier.metricInner, hF] using hw
  rw [hmetric]
  simpa [SmoothSpacetimeEmbedding.pullbackInnerValue_of_spatial,
    FlowCarrier.metricInner] using hN k hkN t ht x hx v w hnormv hnormw

end PoincareConjecture.ChartDistance

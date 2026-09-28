import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.JetConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChosenChart
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance



theorem pullback_metric_CInfinity_of_quotient_coefficient_jets
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
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ Ioo T' T, ∀ i (x : Piece U i) v w,
        (gLimit t i).inner x v w = B i (t, x) v w)
    (E : ℕ → Set (Quotient O.setoid)) (hE : ∀ k, IsOpen (E k))
    (hEmono : Monotone E) (f : ∀ k, Quotient O.setoid → (D k).carrier)
    (hemb : ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier := (D k).chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    (hjets :
      letI : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
      letI : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
        fun k => (D k).chartedSpace
      letI : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
      ∀ i m K, IsCompact K → K ⊆ Ioo T' T ×ˢ U i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((G k).flow.metric z.1).pullbackCoefficients
              (chartParametrization U hU (f k ∘ O.include i)) z.2))
        (iteratedFDeriv ℝ m (B i)) atTop K) :
    let C := O.flowCarrier U hU hO hclosed
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    ∀ (q : C.carrier) (j r : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K →
      K ⊆ {p | p.1 ∈ Ioo T' T ∧ p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ E j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ p ∈ K,
          ‖MetricJet r
              (C.coordinateCoefficient q
                (pullbackInnerValue F (G k)
                  (SmoothSpacetimeEmbedding.of_spatial F (G k)
                    (hE k) (f k) (hemb k) (hf k) (Ioo T' T))) a b) K p -
            MetricJet r
              (C.coordinateCoefficient q
                (fun t x v w => C.metricInner (F.metricAt t) x v w) a b) K p‖ < ε := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  let C := O.flowCarrier U hU hO hclosed
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
    fun k => (D k).chartedSpace
  let : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
  apply SmoothSpacetimeEmbedding.pullback_metric_CInfinity_of_spatial_jets
    F G E hE hEmono f hemb hf
  intro q m K hK hKchart
  obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q
  have hKU : K ⊆ Ioo T' T ×ˢ U i := by
    simpa only [htarget] using hKchart
  have hlimit : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (F.flow.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2)
      (B i) (Ioo T' T ×ˢ U i) := by
    rw [hF, hinverse]
    exact quotientMetric_family_pullbackCoefficients_eqOn U hU O hO
      (fun i t => gLimit t i) hcompat B hB i
  have hsource (k : ℕ) :=
    chosenChart_spacetime_pullbackCoefficients_iteratedFDeriv_eq U hU O q i hinverse
      (G k).flow.metric (fun _ => f k) m
  apply ((hjets i m K hK hKU).congr ?_).congr_right ?_
  · exact Eventually.of_forall fun k p _ => congrFun (hsource k).symm p
  · intro p hp
    exact ((eqOn_iteratedFDeriv_of_isOpen (isOpen_Ioo.prod (hU i)) hlimit m)
      (hKU hp)).symm

end PoincareConjecture.ChartDistance

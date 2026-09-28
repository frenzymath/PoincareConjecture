import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.BallTransfer













set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence



theorem eventually_curvatureTensorNorm_le
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (G : PointedGeometricConvergence H.sequence) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Ioo T' T,
      ∀ x ∈ G.limitFlow.ballAt s A, ∀ᶠ k : ℕ in atTop,
        let C := H.sequence.carrier (G.subsequence k)
        letI : TopologicalSpace C.carrier := C.topologicalSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
        letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
        ∀ t ∈ Ioo T' T,
          ((H.sequence.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm
            ((G.embedding k).toFun (t, x)).2 ≤ K := by
  obtain ⟨K, hK, hbound⟩ := H.all_time_curvature_control (2 * A) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro s hs x hx
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := x))
  have hxj : x ∈ G.exhaustion j := hj (mem_singleton x)
  have hsub := G.subsequence_strictMono.tendsto_atTop.eventually hbound
  filter_upwards [hsub, G.eventually_mem_ballAt H.time_bounds hs hx,
    eventually_ge_atTop j] with k hk hball hjk
  let C := H.sequence.carrier (G.subsequence k)
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  intro t ht
  have htime := (G.embedding k).spatial_eq_of_mem ht hs (G.exhaustion_monotone hjk hxj)
  rw [htime]
  exact hk s hs t ht _ hball







theorem curvatureTensorNorm_le_of_tendsto
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (G : PointedGeometricConvergence H.sequence) (A : ℝ) (hA : 0 < A)
    (hcurv_tendsto : letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace;
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace;
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold;
      ∀ s ∈ Ioo T' T, ∀ x ∈ G.limitFlow.ballAt s A,
      ∀ t ∈ Ioo T' T,
        Tendsto (fun k : ℕ =>
          let C := H.sequence.carrier (G.subsequence k)
          letI : TopologicalSpace C.carrier := C.topologicalSpace
          letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
          letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
          ((H.sequence.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm
            ((G.embedding k).toFun (t, x)).2)
          Filter.atTop (𝓝 ((G.limitFlow.flow.connection t).curvatureTensorNorm x))) :
    (letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace;
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace;
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold;
      ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Ioo T' T,
      ∀ x ∈ G.limitFlow.ballAt s A, ∀ t ∈ Ioo T' T,
        (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤ K) := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨K, hK, hbound⟩ := eventually_curvatureTensorNorm_le H G A hA
  refine ⟨K, hK, ?_⟩
  intro s hs x hx t ht
  apply le_of_tendsto (hcurv_tendsto s hs x hx t ht)
  filter_upwards [hbound s hs x hx] with k hk
  exact hk t ht

end PoincareConjecture.PointedGeometricConvergence

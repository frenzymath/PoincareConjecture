import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.LocalDiffeomorphism
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.TimeMetricComparison








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
  {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}



noncomputable def spatialOpenPartialHomeomorph
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    OpenPartialHomeomorph C.carrier D.carrier := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let f := fun x : C.carrier => (e.toFun (t, x)).2
  let g := fun x : D.carrier => (e.inverse (t, x)).2
  have hleft (x : C.carrier) (hx : x ∈ U) : g (f x) = x := by
    have h := congrArg Prod.snd (e.left_inverse (t, x) ⟨ht, hx⟩)
    have heq : e.toFun (t, x) = (t, f x) := Prod.ext (e.time_preserving t x) rfl
    simpa only [heq, g] using h
  refine
    { toFun := f
      invFun := g
      source := U
      target := f '' U
      map_source' := fun x hx => mem_image_of_mem f hx
      map_target' := ?_
      left_inv' := hleft
      right_inv' := ?_
      open_source := hU
      open_target := e.spatialMap_isOpen_image hU ht
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · rintro y ⟨x, hx, rfl⟩
    rw [hleft x hx]
    exact hx
  · rintro y ⟨x, hx, rfl⟩
    rw [hleft x hx]
  · exact fun x hx => (e.spatialMap_contMDiffAt hU ht hx).continuousAt.continuousWithinAt
  · rintro y ⟨x, hx, rfl⟩
    exact (e.spatialInverse_contMDiffAt hU ht hx).continuousAt.continuousWithinAt

theorem spatialOpenPartialHomeomorph_smooth
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e.spatialOpenPartialHomeomorph hU ht)
      (e.spatialOpenPartialHomeomorph hU ht).source ∧
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e.spatialOpenPartialHomeomorph hU ht).symm
      (e.spatialOpenPartialHomeomorph hU ht).target := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  constructor
  · exact fun x hx => (e.spatialMap_contMDiffAt hU ht hx).contMDiffWithinAt
  · rintro y ⟨x, hx, rfl⟩
    exact (e.spatialInverse_contMDiffAt hU ht hx).contMDiffWithinAt

end PoincareConjecture.SmoothSpacetimeEmbedding

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}


noncomputable def sourceCoordinateChart (G : PointedGeometricConvergence S)
    (hT : T' < 0 ∧ 0 < T) (k : ℕ) (q : G.limitCarrier.carrier) :
    letI : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).topologicalSpace
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).topologicalSpace
  exact (chartAt (EuclideanSpace ℝ (Fin n)) q).symm.trans
    ((G.embedding k).spatialOpenPartialHomeomorph (G.exhaustion_open k) hT)

theorem sourceCoordinateChart_smooth (G : PointedGeometricConvergence S)
    (hT : T' < 0 ∧ 0 < T) (k : ℕ) (q : G.limitCarrier.carrier) :
    letI : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).chartedSpace
    letI : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).isManifold
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (G.sourceCoordinateChart hT k q)
      (G.sourceCoordinateChart hT k q).source ∧
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (G.sourceCoordinateChart hT k q).symm
      (G.sourceCoordinateChart hT k q).target := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).chartedSpace
  let : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).isManifold
  obtain ⟨hf, hi⟩ := (G.embedding k).spatialOpenPartialHomeomorph_smooth (G.exhaustion_open k) hT
  constructor
  · exact hf.comp (contMDiffOn_chart_symm.mono inter_subset_left) inter_subset_right
  · exact contMDiffOn_chart.comp (hi.mono inter_subset_left) inter_subset_right



theorem eventually_subset_sourceCoordinateChart (G : PointedGeometricConvergence S)
    (hT : T' < 0 ∧ 0 < T) (q : G.limitCarrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
      A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∀ᶠ k : ℕ in atTop, A ⊆ (G.sourceCoordinateChart hT k q).source := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let c := chartAt (EuclideanSpace ℝ (Fin n)) q
  have hcompact : IsCompact (c.symm '' A) := hA.image_of_continuousOn (c.symm.continuousOn.mono hchart)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  exact ⟨hchart hx, G.exhaustion_monotone hk (hj (mem_image_of_mem c.symm hx))⟩

end PoincareConjecture.PointedGeometricConvergence

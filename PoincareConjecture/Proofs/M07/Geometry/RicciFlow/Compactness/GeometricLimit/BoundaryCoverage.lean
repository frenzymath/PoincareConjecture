import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.LocalDiffeomorphism
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceBallCoverage

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem RiemannianMetric.isPreconnected_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    IsPreconnected (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply isPreconnected_of_forall p
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  refine ⟨γ '' Icc (0 : ℝ) 1, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩,
    ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩,
    isPreconnected_Icc.image γ hγ.continuousOn⟩
  rintro _ ⟨s, hs, rfl⟩
  exact lt_of_le_of_lt
    ((Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl hs.2)) hγ0 rfl hs.1).trans
      (Manifold.pathELength_mono le_rfl hs.2)) hlength

namespace SmoothSpacetimeEmbedding

set_option backward.isDefEq.respectTransparency false in

theorem ball_subset_spatial_image_of_boundary_avoided
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D}
    {U V : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U)
    (hV : @IsOpen C.carrier C.topologicalSpace V)
    (hcompact : @IsCompact C.carrier C.topologicalSpace
      (@closure C.carrier C.topologicalSpace V))
    (hVU : @closure C.carrier C.topologicalSpace V ⊆ U)
    (hp : F.base ∈ V) {t A : ℝ} (ht : t ∈ Ioo T' T) (hA : 0 < A)
    (hboundary : ∀ x ∈ @frontier C.carrier C.topologicalSpace V,
      ENNReal.ofReal A ≤ (D.metricEMetricSpace (G.metricAt t)).edist
        (e.toFun (t, F.base)).2 (e.toFun (t, x)).2) :
    D.metricBall (G.metricAt t) (e.toFun (t, F.base)).2 A ⊆
      (fun x => (e.toFun (t, x)).2) '' V := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let : T2Space D.carrier := D.t2Space
  let f : C.carrier → D.carrier := fun x => (e.toFun (t, x)).2
  have hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x :=
    fun x hx => e.spatialMap_contMDiffAt hU ht hx
  have hopen : IsOpen (f '' V) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
      (hf x (hVU (subset_closure hx)))
      (e.spatialMap_mfderiv_bijective hU ht (hVU (subset_closure hx)))]
    exact image_mem_map (hV.mem_nhds hx)
  have hclosed : IsClosed (f '' closure V) :=
    (hcompact.image_of_continuousOn
      (fun x hx => (hf x (hVU hx)).continuousAt.continuousWithinAt)).isClosed
  have hclosure : closure (f '' V) ⊆ f '' closure V :=
    closure_minimal (image_mono subset_closure) hclosed
  apply (G.metricAt t).isPreconnected_ball (f F.base) A
    |>.subset_of_closure_inter_subset hopen
  · refine ⟨f F.base, ?_, mem_image_of_mem f hp⟩
    change (G.metricAt t).edist (f F.base) (f F.base) < ENNReal.ofReal A
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hA
  · rintro y ⟨hyclosure, hyball⟩
    obtain ⟨x, hx, rfl⟩ := hclosure hyclosure
    have hxV : x ∈ V := by
      by_contra hxV
      have hfront : x ∈ frontier V := by
        rw [frontier, hV.interior_eq]
        exact ⟨hx, hxV⟩
      exact (not_lt_of_ge (hboundary x hfront)) hyball
    exact mem_image_of_mem f hxV

end SmoothSpacetimeEmbedding

namespace PointedGeometricConvergence

theorem source_ball_coverage_of_boundary_escape
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ @frontier G.limitCarrier.carrier G.limitCarrier.topologicalSpace
          (G.exhaustion j),
        ENNReal.ofReal A ≤
          ((S.carrier (G.subsequence k)).metricEMetricSpace
            ((S.flow (G.subsequence k)).metricAt 0)).edist
              (S.flow (G.subsequence k)).base ((G.embedding k).toFun (0, x)).2) :
    ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  intro A hA
  obtain ⟨j, hj⟩ := hescape A hA
  obtain ⟨l, hl⟩ := G.exists_exhaustion_superset (G.exhaustion_compactClosure j)
  refine ⟨j, ?_⟩
  filter_upwards [hj, eventually_ge_atTop l] with k hk hlk
  have hbound : ∀ x ∈ frontier (G.exhaustion j),
      ENNReal.ofReal A ≤
        ((S.carrier (G.subsequence k)).metricEMetricSpace
          ((S.flow (G.subsequence k)).metricAt 0)).edist
            ((G.embedding k).toFun (0, G.limitFlow.base)).2
            ((G.embedding k).toFun (0, x)).2 := by
    simpa only [G.base_preserving k] using hk
  have hcover := (G.embedding k).ball_subset_spatial_image_of_boundary_avoided
    (G.exhaustion_open k) (G.exhaustion_open j) (G.exhaustion_compactClosure j)
    (hl.trans (G.exhaustion_monotone hlk)) (G.base_in_exhaustion j) hT hA hbound
  simpa only [G.base_preserving k, BasedFlow.zeroBall, BasedFlow.metricAt] using hcover

theorem metricComplete_zero_of_boundary_escape
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ @frontier G.limitCarrier.carrier G.limitCarrier.topologicalSpace
          (G.exhaustion j),
        ENNReal.ofReal A ≤
          ((S.carrier (G.subsequence k)).metricEMetricSpace
            ((S.flow (G.subsequence k)).metricAt 0)).edist
              (S.flow (G.subsequence k)).base ((G.embedding k).toFun (0, x)).2) :
    G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) :=
  G.metricComplete_zero_of_source_ball_coverage hT
    (G.source_ball_coverage_of_boundary_escape hT hescape)

end PointedGeometricConvergence

end PoincareConjecture

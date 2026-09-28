import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence




theorem source_ball_coverage_of_boundary_control
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)] [∀ k, T2Space (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) {R : ℝ} (hR : 0 < R)
    (hboundary : letI := G.limitCarrier.topologicalSpace
      ∃ l : ℕ, ∀ᶠ j in atTop, ∀ q ∈ frontier (G.exhaustion l),
        ENNReal.ofReal R ≤ (g (G.subsequence j)).edist
          (p (G.subsequence j)) (G.embedding j q)) :
    ∃ l : ℕ, ∀ᶠ j in atTop,
      (g (G.subsequence j)).ball (p (G.subsequence j)) R ⊆
        G.embedding j '' G.exhaustion l := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun i => subset_closure.trans (G.exhaustion_step i))
  obtain ⟨l, hboundary⟩ := hboundary
  refine ⟨l, ?_⟩
  filter_upwards [hboundary, eventually_ge_atTop (l + 1)] with j hj hlj
  have hbuffer : closure (G.exhaustion l) ⊆ G.exhaustion j :=
    (G.exhaustion_step l).trans (hmono hlj)
  let f := G.embedding j
  have himage : f '' G.exhaustion l =
      (fun x : G.exhaustion j => f x) ''
        ((Subtype.val : G.exhaustion j → G.limitCarrier.carrier) ⁻¹' G.exhaustion l) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hbuffer (subset_closure hx)⟩, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.val, hx, hxy⟩
  have hopen : IsOpen (f '' G.exhaustion l) := by
    rw [himage]
    exact (G.embedding_open j).isOpenMap _
      ((G.exhaustion_open l).preimage continuous_subtype_val)
  have hcontinuous : ContinuousOn f (closure (G.exhaustion l)) := by
    intro x hx
    exact (G.embedding_smooth j ⟨x, hbuffer hx⟩).contMDiffAt.continuousAt.continuousWithinAt
  have hclosed : IsClosed (f '' closure (G.exhaustion l)) :=
    ((G.exhaustion_compactClosure l).image_of_continuousOn hcontinuous).isClosed
  have hclosure : closure (f '' G.exhaustion l) ⊆ f '' closure (G.exhaustion l) :=
    closure_minimal (image_mono subset_closure) hclosed
  apply IsPreconnected.subset_of_closure_inter_subset
    ((g (G.subsequence j)).isPreconnected_ball (p (G.subsequence j)) R) hopen
  · refine ⟨p (G.subsequence j), ?_, G.base, G.base_in_exhaustion l,
      G.base_preserving j⟩
    change (g (G.subsequence j)).edist (p (G.subsequence j)) (p (G.subsequence j)) <
      ENNReal.ofReal R
    have hself : (g (G.subsequence j)).edist
        (p (G.subsequence j)) (p (G.subsequence j)) = 0 := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 n) : M (G.subsequence j) → Type _) :=
        ⟨(g (G.subsequence j)).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hR
  · rintro y ⟨hyclosure, hyball⟩
    obtain ⟨x, hx, rfl⟩ := hclosure hyclosure
    have hxV : x ∈ G.exhaustion l := by
      by_contra hxV
      have hfront : x ∈ frontier (G.exhaustion l) := by
        rw [frontier, (G.exhaustion_open l).interior_eq]
        exact ⟨hx, hxV⟩
      exact (not_lt_of_ge (hj x hfront)) hyball
    exact mem_image_of_mem f hxV




theorem source_ball_coverage
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)] [∀ k, T2Space (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) {R : ℝ} (hR : 0 < R) (hRA : R < A) :
    ∃ l : ℕ, ∀ᶠ j in atTop,
      (g (G.subsequence j)).ball (p (G.subsequence j)) R ⊆
        G.embedding j '' G.exhaustion l :=
  G.source_ball_coverage_of_boundary_control hR (G.boundary_control R hRA)

end PoincareConjecture.M30.PartialPointedMetricConvergence

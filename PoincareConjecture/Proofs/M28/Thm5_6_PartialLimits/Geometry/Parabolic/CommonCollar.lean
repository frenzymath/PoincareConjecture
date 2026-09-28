import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SharedExport
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage











set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Filter Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u}
  [∀ k, TopologicalSpace (M k)]
  [∀ k, T2Space (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)}
  {p : ∀ k, M k} {A : ℝ}







theorem PartialPointedFlowConvergence.exists_eventual_source_ball_image
    (G : PartialPointedFlowConvergence F p A 0)
    {B : ℝ} (hB : 0 < B) (hBA : B < A) :
    ∃ l : ℕ, ∀ᶠ j in atTop,
      ((F (G.subsequence j)).metric 0).ball (p (G.subsequence j)) B ⊆
        G.embedding j '' G.exhaustion l := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨l, hl⟩ := G.boundary_control B hBA
  have hstep : ∀ i, G.exhaustion i ⊆ G.exhaustion (i + 1) := by
    intro i
    exact subset_closure.trans (G.exhaustion_step i)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ hstep
  refine ⟨l, ?_⟩
  filter_upwards [hl, eventually_ge_atTop (l + 1)] with j hj hjl
  have hlj : l + 1 ≤ j := hjl
  have hclj : closure (G.exhaustion l) ⊆ G.exhaustion j := by
    exact (G.exhaustion_step l).trans (hmono hlj)
  have hVj : G.exhaustion l ⊆ G.exhaustion j :=
    subset_closure.trans hclj
  have hopen : IsOpen (G.embedding j '' G.exhaustion l) := by
    let Vj : Set (G.exhaustion j) :=
      (fun x : G.exhaustion j => (x : G.limitCarrier.carrier)) ⁻¹'
        G.exhaustion l
    have hVjopen : IsOpen Vj := by
      exact (G.exhaustion_open l).preimage continuous_subtype_val
    have himage :
        (fun x : G.exhaustion j => G.embedding j (x : G.limitCarrier.carrier)) '' Vj =
          G.embedding j '' G.exhaustion l := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hVj hx⟩, hx, rfl⟩
    rw [← himage]
    exact (G.embedding_open j).isOpenMap _ hVjopen
  have hcont : ContinuousOn (G.embedding j) (closure (G.exhaustion l)) := by
    intro x hx
    have hxj : x ∈ G.exhaustion j := hclj hx
    exact ((G.embedding_smooth j).contMDiffOn x hxj).continuousWithinAt.mono hclj
  have hclosed : IsClosed (G.embedding j '' closure (G.exhaustion l)) :=
    (G.exhaustion_compactClosure l).image_of_continuousOn hcont |>.isClosed
  have hclosure : closure (G.embedding j '' G.exhaustion l) ⊆
      G.embedding j '' closure (G.exhaustion l) :=
    closure_minimal (image_mono subset_closure) hclosed
  have hconn : IsPreconnected
      ((F (G.subsequence j)).metric 0 |>.ball (p (G.subsequence j)) B) :=
    RiemannianMetric.isPreconnected_ball _ _ _
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M (G.subsequence j) → Type _) :=
    ⟨((F (G.subsequence j)).metric 0).toRiemannianMetric⟩
  let : ∀ x : M (G.subsequence j), ENormSMulClass ℝ (TangentSpace (𝓡 n) x) :=
    fun _ ↦ inferInstance
  apply hconn.subset_of_closure_inter_subset hopen
  · refine ⟨G.embedding j G.base, ?_, mem_image_of_mem _
      (G.base_in_exhaustion l)⟩
    rw [G.base_preserving j]
    change Manifold.riemannianEDist (𝓡 n)
      (p (G.subsequence j)) (p (G.subsequence j)) < ENNReal.ofReal B
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hB
  · rintro y ⟨hyclosure, hyball⟩
    obtain ⟨x, hx, rfl⟩ := hclosure hyclosure
    have hxV : x ∈ G.exhaustion l := by
      by_contra hxV
      have hfront : x ∈ frontier (G.exhaustion l) := by
        rw [frontier, (G.exhaustion_open l).interior_eq]
        exact ⟨hx, hxV⟩
      exact (not_lt_of_ge (hj x hfront)) hyball
    exact mem_image_of_mem _ hxV



theorem PartialLimitWindowExport.exists_eventual_source_ball_image
    (E : PartialLimitWindowExport F p A)
    {B : ℝ} (hB : 0 < B) (hBA : B < A) :
    ∃ l : ℕ, ∀ᶠ j in atTop,
      ((F (E.limit.subsequence j)).metric 0).ball
          (p (E.limit.subsequence j)) B ⊆
        E.limit.embedding j '' E.limit.exhaustion l :=
  E.limit.exists_eventual_source_ball_image hB hBA



theorem PartialLimitWindowExport.exists_eventual_compact_collar
    (E : PartialLimitWindowExport F p A)
    {B : ℝ} (hB : 0 < B) (hBA : B < A) :
    ∃ l : ℕ,
      @IsCompact E.limit.limitCarrier.carrier E.limit.limitCarrier.topologicalSpace
        (@closure E.limit.limitCarrier.carrier E.limit.limitCarrier.topologicalSpace
          (E.limit.exhaustion l)) ∧
      ∀ᶠ j in atTop,
        ((F (E.limit.subsequence j)).metric 0).ball
            (p (E.limit.subsequence j)) B ⊆
          E.limit.embedding j '' E.limit.exhaustion l := by
  obtain ⟨l, hcover⟩ := E.exists_eventual_source_ball_image hB hBA
  exact ⟨l, E.limit.exhaustion_compactClosure l, hcover⟩

end PoincareConjecture.M28

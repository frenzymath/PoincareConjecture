import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Interior.Dense
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Interior.LocalPathConnected

noncomputable section

open Set Filter Metric
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

private theorem isPreconnected_of_dense_local
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {s : Set X} (hdense : Dense s)
    (hlocal : ∀ x : X, ∃ U ∈ 𝓝 x, IsPreconnected (U ∩ s)) :
    IsPreconnected s := by
  intro u v hu hv hcover hsu hsv
  have hclosedcover : (univ : Set X) ⊆ closure (s ∩ u) ∪ closure (s ∩ v) := by
    have hs : s ⊆ closure (s ∩ u) ∪ closure (s ∩ v) := by
      intro x hx
      rcases hcover hx with hxu | hxv
      · exact Or.inl (subset_closure ⟨hx, hxu⟩)
      · exact Or.inr (subset_closure ⟨hx, hxv⟩)
    simpa only [hdense.closure_eq, (isClosed_closure.union isClosed_closure).closure_eq]
      using closure_mono hs
  obtain ⟨x, _, hxu, hxv⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
    (closure (s ∩ u)) (closure (s ∩ v)) isClosed_closure isClosed_closure
    hclosedcover
    (by obtain ⟨x, hx⟩ := hsu; exact ⟨x, mem_univ x, subset_closure hx⟩)
    (by obtain ⟨x, hx⟩ := hsv; exact ⟨x, mem_univ x, subset_closure hx⟩)
  obtain ⟨U, hU, hconn⟩ := hlocal x
  obtain ⟨a, haU, has, hau⟩ := mem_closure_iff_nhds.mp hxu U hU
  obtain ⟨b, hbU, hbs, hbv⟩ := mem_closure_iff_nhds.mp hxv U hU
  obtain ⟨z, hz, hzu, hzv⟩ := hconn u v hu hv
    (fun y hy => hcover hy.2) ⟨a, ⟨haU, has⟩, hau⟩ ⟨b, ⟨hbU, hbs⟩, hbv⟩
  exact ⟨z, hz.2, hzu, hzv⟩

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_preconnected_interior_nhds (x : M) :
    ∃ U ∈ 𝓝 x, IsPreconnected (U ∩ I.interior M) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (extChartAt_target_union_compl_range_mem_nhds_of_mem (mem_extChartAt_target (I := I) x))
  let C := ball (extChartAt I x x) r ∩ interior (range I)
  have hC : C ⊆ (extChartAt I x).target := by
    intro z hz
    exact (hball hz.1).resolve_right (not_not.mpr (interior_subset hz.2))
  let U := (extChartAt I x).source ∩ extChartAt I x ⁻¹' ball (extChartAt I x x) r
  have hU : U ∈ 𝓝 x := (isOpen_extChartAt_preimage' x isOpen_ball).mem_nhds
    ⟨mem_extChartAt_source x, mem_ball_self hr⟩
  refine ⟨U, hU, ?_⟩
  have heq : U ∩ I.interior M = (extChartAt I x).symm '' C := by
    ext y
    constructor
    · rintro ⟨⟨hys, hyball⟩, hyint⟩
      have hycoord := (I.isInteriorPoint_iff_of_mem_atlas
        (by simp : (∞ : WithTop ℕ∞) ≠ 0) (chart_mem_atlas H x)
        (by simpa only [extChartAt_source] using hys)).mp hyint
      exact ⟨extChartAt I x y, ⟨hyball,
        (chartAt H x).interior_extend_target_subset_interior_range hycoord⟩,
        (extChartAt I x).left_inv hys⟩
    · rintro ⟨z, hz, rfl⟩
      have hzt := hC hz
      have hys := (extChartAt I x).map_target hzt
      refine ⟨⟨hys, ?_⟩, ?_⟩
      · simpa only [mem_preimage, (extChartAt I x).right_inv hzt] using hz.1
      · apply (I.isInteriorPoint_iff_of_mem_atlas
          (by simp : (∞ : WithTop ℕ∞) ≠ 0) (chart_mem_atlas H x)
          (by simpa only [extChartAt_source] using hys)).2
        change extChartAt I x ((extChartAt I x).symm z) ∈ interior (extChartAt I x).target
        rw [(extChartAt I x).right_inv hzt]
        exact (extChartAt_target_eventuallyEq_of_mem hzt).symm.mem_interior hz.2
  rw [heq]
  exact ((convex_ball _ _).inter I.convex_range.interior).isPreconnected.image
    (extChartAt I x).symm ((continuousOn_extChartAt_symm x).mono hC)

theorem isPathConnected_manifoldInterior [ConnectedSpace M] :
    IsPathConnected (I.interior M) := by
  let : LocallyPathConnectedSpace M := manifold_locallyPathConnected (I := I)
  apply (I.isOpen_interior (by simp : (∞ : WithTop ℕ∞) ≠ 0)).isConnected_iff_isPathConnected.mp
  exact ⟨(dense_manifoldInterior (I := I)).nonempty,
    isPreconnected_of_dense_local (dense_manifoldInterior (I := I))
      (exists_preconnected_interior_nhds (I := I))⟩

end Poincare.Manifold

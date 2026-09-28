import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.GeneralPosition

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem preconnected_subset_chartDisk_or_compl (q : M) {r : ℝ}
    (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target)
    {A : Set M} (hA : IsPreconnected A) (hdisjoint : Disjoint A (chartCircle q r)) :
    A ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ∨
      A ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r)ᶜ := by
  let D := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
    closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r
  have hclosed : IsClosed D := (isCompact_chart_closedBall q htarget).isClosed
  have hinterior : interior D = (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r := by
    dsimp only [D]
    rw [interior_chart_image q htarget, interior_closedBall _ hr.ne']
  have hfrontier : frontier D = chartCircle q r := by
    dsimp only [D]
    rw [frontier_chart_image q (isCompact_closedBall _ _) htarget,
      frontier_closedBall _ hr.ne']
    rfl
  have hcover : A ⊆ interior D ∪ interior Dᶜ := by
    rw [← compl_frontier_eq_union_interior, hfrontier]
    exact disjoint_left.mp hdisjoint
  have hsep : Disjoint (interior D) (interior Dᶜ) :=
    disjoint_left.mpr fun x hx hx' => (interior_subset hx') (interior_subset hx)
  simpa only [hinterior, hclosed.isOpen_compl.interior_eq] using
    hA.subset_or_subset isOpen_interior isOpen_interior hsep hcover

theorem connectedComponentIn_subset_chartDisk_or_compl (q : M) {r : ℝ}
    (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target)
    {K : Set M} (hcircle : chartCircle q r ⊆ K) (x : M) :
    connectedComponentIn Kᶜ x ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
          ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ∨
      connectedComponentIn Kᶜ x ⊆
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r)ᶜ := by
  apply preconnected_subset_chartDisk_or_compl q hr htarget
    isPreconnected_connectedComponentIn
  exact disjoint_left.mpr fun z hz hzCircle =>
    connectedComponentIn_subset Kᶜ x hz (hcircle hzCircle)

theorem connectedComponentIn_ne_of_inside_outside_chartDisk (q : M) {r : ℝ}
    (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target)
    {K : Set M} (hcircle : chartCircle q r ⊆ K)
    {x y : M} (hx : x ∉ K) (hy : y ∉ K)
    (hinside : x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r)
    (houtside : y ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r) :
    connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ y := by
  intro heq
  rcases connectedComponentIn_subset_chartDisk_or_compl q hr htarget hcircle x with hin | hout
  · have hymem : y ∈ connectedComponentIn Kᶜ x := heq.symm ▸ mem_connectedComponentIn hy
    exact houtside (image_mono ball_subset_closedBall (hin hymem))
  · exact hout (mem_connectedComponentIn hx) (image_mono ball_subset_closedBall hinside)

theorem exists_distinct_components_near_chartCircle (q : M) {r : ℝ}
    (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target)
    {K : Set M} (hcircle : chartCircle q r ⊆ K)
    {p : M} (hp : p ∈ chartCircle q r) {N s : Set M}
    (hN : N ∈ 𝓝 p) (hlocal : ∀ z ∈ N, z ∈ K ↔ z ∈ chartCircle q r)
    (hs : s ∈ 𝓝 p) :
    ∃ x ∈ s, ∃ y ∈ s, x ∉ K ∧ y ∉ K ∧
      x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ∧
      y ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ∧
      connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ y := by
  let D := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
    closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r
  let U := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm ''
    ball (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r
  have hclosed : IsClosed D := (isCompact_chart_closedBall q htarget).isClosed
  have hinterior : interior D = U := by
    dsimp only [D]
    rw [interior_chart_image q htarget, interior_closedBall _ hr.ne']
  have hfrontier : frontier D = chartCircle q r := by
    dsimp only [D]
    rw [frontier_chart_image q (isCompact_closedBall _ _) htarget,
      frontier_closedBall _ hr.ne']
    rfl
  have hpfront : p ∈ frontier D := hfrontier.symm ▸ hp
  have hpU : p ∈ closure U := by
    rw [show closure U = D from closure_chart_ball q hr htarget]
    exact hclosed.frontier_subset hpfront
  have hpout : p ∈ closure Dᶜ := by
    apply frontier_subset_closure
    simpa only [frontier_compl] using hpfront
  obtain ⟨x, ⟨hxs, hxN⟩, hxU⟩ :=
    mem_closure_iff_nhds.mp hpU (s ∩ N) (Filter.inter_mem hs hN)
  obtain ⟨y, ⟨hys, hyN⟩, hyout⟩ :=
    mem_closure_iff_nhds.mp hpout (s ∩ N) (Filter.inter_mem hs hN)
  have hxK : x ∉ K := by
    intro hxK
    have hxfront : x ∈ frontier D := hfrontier.symm ▸ (hlocal x hxN).mp hxK
    exact hxfront.2 (hinterior.symm ▸ hxU)
  have hyK : y ∉ K := by
    intro hyK
    have hyfront : y ∈ frontier D := hfrontier.symm ▸ (hlocal y hyN).mp hyK
    exact hyout (hclosed.frontier_subset hyfront)
  exact ⟨x, hxs, y, hys, hxK, hyK, hxU, hyout,
    connectedComponentIn_ne_of_inside_outside_chartDisk q hr htarget hcircle hxK hyK hxU hyout⟩

end PoincareConjecture.Topology.Surface

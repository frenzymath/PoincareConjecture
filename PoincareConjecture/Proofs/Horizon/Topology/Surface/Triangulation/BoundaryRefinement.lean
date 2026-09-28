


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Refinement













set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_parametrized_chart_disk_boundary_refinement_of_finite_intersections
    (s : Finset M) (r : M → ℝ)
    (hr : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hinter : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) y y) (r y)).Finite) :
    ∃ (n : (s × Fin 2) → ℕ) (c : ∀ i, Fin (n i + 1) → ℝ)
      (edge : ∀ i, Fin (n i) → SmoothEdge M),
      (∀ i, 0 < n i) ∧
      (∀ i k, InjOn (edge i k).map (Icc (0 : ℝ) 1)) ∧
      (∀ x : s, (⋃ i : Fin 2, ⋃ k, (edge (x, i) k).map '' Icc (0 : ℝ) 1) =
        frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) (x : M)).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (r x))) ∧
      (∀ p q : Σ i, Fin (n i), p ≠ q →
        (edge p.1 p.2).map '' Icc (0 : ℝ) 1 ∩ (edge q.1 q.2).map '' Icc (0 : ℝ) 1 ⊆
        {(edge p.1 p.2).map 0, (edge p.1 p.2).map 1} ∩
          {(edge q.1 q.2).map 0, (edge q.1 q.2).map 1}) ∧
      (∀ i, StrictMono (c i) ∧ c i 0 = 0 ∧ c i (Fin.last (n i)) = 1) ∧
      (∀ i k t, (edge i k).map t =
        (chartAt (EuclideanSpace ℝ (Fin 2)) (i.1 : M)).symm
          (coordinateCircleArc
            (chartAt (EuclideanSpace ℝ (Fin 2)) (i.1 : M) i.1) (r i.1)
            ((i.2 : ℝ) * Real.pi)
            (c i k.castSucc + t * (c i k.succ - c i k.castSucc)))) := by
  classical
  have hcircle (x : s) : sphere (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (r x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M)).target :=
    sphere_subset_closedBall.trans (htarget x x.property)
  choose arc hmap hinj harc using fun x : s =>
    exists_smoothEdges_of_chartCircle (M := M) x
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (hr x x.property) (hcircle x)
  let arcs : (s × Fin 2) → SmoothEdge M := fun i => arc i.1 i.2
  have hsub (x : s) (i : Fin 2) : (arc x i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M)).symm ''
        sphere (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (r x) := by
    rw [← harc x]
    exact subset_iUnion (fun j : Fin 2 => (arc x j).map '' Icc (0 : ℝ) 1) i
  have hfinite (i j : s × Fin 2) (hij : i ≠ j) :
      ((arcs i).map '' Icc (0 : ℝ) 1 ∩ (arcs j).map '' Icc (0 : ℝ) 1).Finite := by
    rcases i with ⟨x, i⟩
    rcases j with ⟨y, j⟩
    by_cases hxy : x = y
    · subst y
      have hij' : i ≠ j := fun h => hij (h ▸ rfl)
      dsimp [arcs]
      rw [hmap x i, hmap x j]
      exact finite_inter_chartCircleArc_images (x : M) _ (hr x x.property) (hcircle x) hij'
    · exact (hinter x x.property y y.property
        (fun h => hxy (Subtype.ext h))).subset (inter_subset_inter (hsub x i) (hsub y j))
  obtain ⟨n, c, edge, hpieces, _, hendpoints⟩ := exists_finite_edge_refinement arcs
    (fun i => hinj i.1 i.2) hfinite
  refine ⟨n, c, edge, fun i => (hpieces i).1,
    fun i => (hpieces i).2.2.2.2.2.1, ?_, hendpoints,
    fun i => ⟨(hpieces i).2.1, (hpieces i).2.2.1, (hpieces i).2.2.2.1⟩, ?_⟩
  · intro x
    have hpiece_cover (i : Fin 2) := (hpieces (x, i)).2.2.2.2.2.2.1
    simp_rw [hpiece_cover]
    rw [frontier_chart_image (x : M) (isCompact_closedBall _ _) (htarget x x.property),
      frontier_closedBall _ (hr x x.property).ne']
    exact harc x
  · intro i k t
    rw [(hpieces i).2.2.2.2.1 k t]
    change (arc i.1 i.2).map _ = _
    rw [hmap i.1 i.2]
    rfl



theorem exists_chart_disk_boundary_refinement_of_finite_intersections
    (s : Finset M) (r : M → ℝ)
    (hr : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hinter : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) y y) (r y)).Finite) :
    ∃ (n : (s × Fin 2) → ℕ)
      (edge : ∀ i, Fin (n i) → SmoothEdge M),
      (∀ i, 0 < n i) ∧
      (∀ i k, InjOn (edge i k).map (Icc (0 : ℝ) 1)) ∧
      (∀ x : s, (⋃ i : Fin 2, ⋃ k, (edge (x, i) k).map '' Icc (0 : ℝ) 1) =
        frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) (x : M)).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (r x))) ∧
      (∀ p q : Σ i, Fin (n i), p ≠ q →
        (edge p.1 p.2).map '' Icc (0 : ℝ) 1 ∩ (edge q.1 q.2).map '' Icc (0 : ℝ) 1 ⊆
        {(edge p.1 p.2).map 0, (edge p.1 p.2).map 1} ∩
          {(edge q.1 q.2).map 0, (edge q.1 q.2).map 1}) := by
  obtain ⟨n, _, edge, hn, hinj, hfrontier, hmeet, _, _⟩ :=
    exists_parametrized_chart_disk_boundary_refinement_of_finite_intersections
      s r hr htarget hinter
  exact ⟨n, edge, hn, hinj, hfrontier, hmeet⟩



theorem exists_finite_chart_disk_boundary_refinement [CompactSpace M] :
    ∃ (s : Finset M) (r : M → ℝ) (n : (s × Fin 2) → ℕ)
      (edge : ∀ i, Fin (n i) → SmoothEdge M),
      (∀ x ∈ s, 0 < r x) ∧
      (∀ x ∈ s, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M) ∧
      (∀ i, 0 < n i) ∧
      (∀ i k, InjOn (edge i k).map (Icc (0 : ℝ) 1)) ∧
      (∀ x : s, (⋃ i : Fin 2, ⋃ k, (edge (x, i) k).map '' Icc (0 : ℝ) 1) =
        frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) (x : M)).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (x : M) x) (r x))) ∧
      (∀ p q : Σ i, Fin (n i), p ≠ q →
        (edge p.1 p.2).map '' Icc (0 : ℝ) 1 ∩ (edge q.1 q.2).map '' Icc (0 : ℝ) 1 ⊆
        {(edge p.1 p.2).map 0, (edge p.1 p.2).map 1} ∩
          {(edge q.1 q.2).map 0, (edge q.1 q.2).map 1}) := by
  obtain ⟨s, r, hr, htarget, hcover, hinter⟩ :=
    exists_finite_chart_ball_cover_finite_intersections (M := M)
  obtain ⟨n, edge, hn, hinj, hfrontier, hmeet⟩ :=
    exists_chart_disk_boundary_refinement_of_finite_intersections s r hr htarget hinter
  exact ⟨s, r, n, edge, hr, htarget, hcover, hn, hinj, hfrontier, hmeet⟩

end PoincareConjecture.Topology.Surface

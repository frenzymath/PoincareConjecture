


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCircle
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartLevel











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



theorem exists_finite_buffered_chart_ball_cover [CompactSpace M] :
    ∃ (s : Finset M) (R : M → ℝ),
      (∀ x, 0 < R x) ∧
      (∀ x, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x / 4)) = (univ : Set M) := by
  classical
  choose R hpos hsub using exists_chart_closedBall_subset (M := M)
  have hsmall (x : M) : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x / 4) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target :=
    (closedBall_subset_closedBall (by linarith [hpos x])).trans (hsub x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x / 4))
    (fun x => isOpen_chart_ball x (hsmall x))
    (by intro x _; exact mem_iUnion.mpr ⟨x, mem_chart_ball x (div_pos (hpos x) (by norm_num))⟩)
  exact ⟨s, R, hpos, hsub, Subset.antisymm (subset_univ _) hs⟩

variable [T2Space M] [IsManifold (𝓡 2) ∞ M]



theorem exists_chart_circle_radii_finite_intersections
    (s : Finset M) (R : M → ℝ) (hpos : ∀ x, 0 < R x)
    (hsub : ∀ x, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ ρ : M → ℝ, (∀ x ∈ s, ρ x ∈ Ioo (R x / 4) (R x / 3)) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (ρ x) ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) y y) (ρ y)).Finite := by
  classical
  let C (x : M) (r : ℝ) := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r
  change ∃ ρ : M → ℝ, (∀ x ∈ s, ρ x ∈ Ioo (R x / 4) (R x / 3)) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (C x (ρ x) ∩ C y (ρ y)).Finite
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨ρ, hρ, hfinite⟩ := ih
      have hedges (y : {y // y ∈ s}) := exists_smoothEdges_of_chartCircle (M := M) y
        (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M) (y : M))
        (show 0 < ρ y from (div_pos (hpos y) (by norm_num)).trans (hρ y y.property).1)
        (show sphere (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M) (y : M)) (ρ y) ⊆
            (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M)).target from
          sphere_subset_closedBall.trans ((closedBall_subset_closedBall
            (by linarith [(hρ y y.property).2, hpos y])).trans (hsub y)))
      choose edge hmap hinj hcover using hedges
      let edges : ({y // y ∈ s} × Fin 2) → SmoothEdge M := fun i => edge i.1 i.2
      obtain ⟨a, ha, hinter⟩ := exists_chart_circle_finite_edge_intersections x edges
        (a := R x / 4) (b := R x / 3) (r := R x / 2) (R := R x)
        (div_pos (hpos x) (by norm_num)) (by linarith [hpos x])
        (by linarith [hpos x]) (by linarith [hpos x]) (hsub x)
      have hnew (y : {y // y ∈ s}) : (C y (ρ y) ∩ C x a).Finite := by
        rw [show C y (ρ y) = ⋃ i, (edge y i).map '' Icc (0 : ℝ) 1 from (hcover y).symm,
          iUnion_inter]
        exact finite_iUnion (fun i => (hinter (y, i)).1)
      refine ⟨Function.update ρ x a, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa using ha
        · have hyx : y ≠ x := fun h => hx (h ▸ hy)
          simpa [hyx] using hρ y hy
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with rfl | hys
        · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
          simpa [Ne.symm hyz, inter_comm] using hnew ⟨z, hzs⟩
        · have hyx : y ≠ x := fun h => hx (h ▸ hys)
          rcases Finset.mem_insert.mp hz with rfl | hzs
          · simpa [hyx] using hnew ⟨y, hys⟩
          · have hzx : z ≠ x := fun h => hx (h ▸ hzs)
            simpa [hyx, hzx] using hfinite y hys z hzs hyz




theorem exists_finite_chart_ball_cover_finite_intersections [CompactSpace M] :
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x ∈ s, 0 < r x) ∧
      (∀ x ∈ s, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) y y) (r y)).Finite := by
  obtain ⟨s, R, hpos, hsub, hcover⟩ := exists_finite_buffered_chart_ball_cover (M := M)
  obtain ⟨r, hr, hinter⟩ := exists_chart_circle_radii_finite_intersections s R hpos hsub
  refine ⟨s, r, ?_, ?_, ?_, hinter⟩
  · intro x hx
    exact (div_pos (hpos x) (by norm_num)).trans (hr x hx).1
  · intro x hx
    exact (closedBall_subset_closedBall (by linarith [(hr x hx).2, hpos x])).trans (hsub x)
  · apply Subset.antisymm (subset_univ _)
    rw [← hcover]
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x, hx,
      ⟨z, ball_subset_ball (hr x hx).1.le hz, rfl⟩⟩

end PoincareConjecture.Topology.Surface

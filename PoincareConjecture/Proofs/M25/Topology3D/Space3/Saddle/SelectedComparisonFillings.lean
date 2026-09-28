import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyDisjointness

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_comparison_fillings
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u) (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (T : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (C : ℝ → Fin 2 → UnitCircle → E2)
    (hC : ∀ i : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C p.1 i p.2))
    (hEmbedding : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 2,
      IsPlanarEmbedding (C t i))
    (hDisjoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Disjoint (range (C t 0)) (range (C t 1)))
    (hStart : ∀ (i : Fin 2) (theta : UnitCircle),
      C 0 i theta = T ((heightPlaneCoordinates u
        (psi (W.leg i (theta, W.level), 0))).1)) :
    ∃ (P : (i : Fin 2) → PlanarSchoenfliesFamilyData (fun t => C t i) 0 1)
      (G : (i : Fin 2) → PlanarFamilyGraphChart (P i)),
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 2),
        ((G i).fiberBallNeighborhood t ht).boundary = range (C t i)) ∧
      (∀ i : Fin 2,
        ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside =
          T '' (W.disc i).inside ∧
        ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
          T '' (W.disc i).closedRegion) ∧
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
        Disjoint ((G 0).fiberBallNeighborhood t ht).closedRegion
          ((G 1).fiberBallNeighborhood t ht).closedRegion) := by
  classical
  have hfamily (i : Fin 2) :
      Nonempty (PlanarSchoenfliesFamilyData (fun t => C t i) 0 1) :=
    hP.2 0 1 (fun t => C t i) zero_lt_one (hC i)
      (fun t ht => hEmbedding t ht i)
  let P : (i : Fin 2) → PlanarSchoenfliesFamilyData (fun t => C t i) 0 1 :=
    fun i => Classical.choice (hfamily i)
  let G : (i : Fin 2) → PlanarFamilyGraphChart (P i) :=
    fun i => Classical.choice ((P i).nonempty_graphChart zero_lt_one)
  have hproject (x : E2) :
      (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (x, W.level))).1 = x := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hboundary (i : Fin 2) :
      ((W.disc i).mapDiffeomorph T).boundary = range (C 0 i) := by
    rw [BallNeighborhoodChart.mapDiffeomorph_boundary]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxlevel : (heightPlaneCoordinates u).symm (x, W.level) ∈
          range (fun theta => psi (W.leg i (theta, W.level), 0)) := by
        rw [← W.disc_boundary i]
        exact ⟨x, hx, rfl⟩
      obtain ⟨theta, htheta⟩ := hxlevel
      dsimp only at htheta
      refine ⟨theta, ?_⟩
      rw [hStart, htheta, hproject]
    · rintro ⟨theta, rfl⟩
      have hlevel : psi (W.leg i (theta, W.level), 0) ∈
          (fun x => (heightPlaneCoordinates u).symm (x, W.level)) ''
            (W.disc i).boundary := by
        rw [W.disc_boundary i]
        exact mem_range_self theta
      obtain ⟨x, hx, hxtheta⟩ := hlevel
      refine ⟨x, hx, ?_⟩
      rw [hStart, ← hxtheta, hproject]
  have hInitial (i : Fin 2) :
      ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside =
        T '' (W.disc i).inside ∧
      ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
        T '' (W.disc i).closedRegion := by
    constructor
    · exact ((G i).fiber_inside_eq 0 ⟨le_rfl, zero_le_one⟩
        ((W.disc i).mapDiffeomorph T) (hboundary i)).trans
          ((W.disc i).mapDiffeomorph_inside T)
    · exact ((G i).fiber_closedRegion_eq 0 ⟨le_rfl, zero_le_one⟩
        ((W.disc i).mapDiffeomorph T) (hboundary i)).trans
          ((W.disc i).mapDiffeomorph_closedRegion T)
  have hstart : Disjoint
      ((G 0).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion
      ((G 1).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion := by
    rw [(hInitial 0).2, (hInitial 1).2]
    exact disjoint_image_of_injective T.injective hnonnested
  refine ⟨P, G, (fun t ht i => (G i).fiberBallNeighborhood_boundary t ht), hInitial, ?_⟩
  exact saddle_planar_family_closedRegion_disjoint (P 0) (P 1) (G 0) (G 1)
    zero_le_one hDisjoint hstart

end PoincareConjecture.M25.Topology3D

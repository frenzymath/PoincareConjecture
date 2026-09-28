import PoincareConjecture.Proofs.M25.Topology3D.Gluing.PlanarFamilyNesting

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_planarFamilyGraphCharts_of_initial_nested_fillings
    (hP : PlanarSchoenfliesService)
    (C : ℝ → Fin 2 → UnitCircle → E2)
    (hSmooth : ∀ l : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C p.1 l p.2))
    (hEmbedding : ∀ t ∈ Icc (0 : ℝ) 1, ∀ l : Fin 2,
      IsPlanarEmbedding (C t l))
    (hDisjoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Disjoint (range (C t 0)) (range (C t 1)))
    (B : Fin 2 → BallNeighborhoodChart E2 E2)
    (hBoundary : ∀ l : Fin 2, (B l).boundary = range (C 0 l))
    (hNested : (B 0).closedRegion ⊆ (B 1).inside) :
    ∃ (PN : (l : Fin 2) →
        PlanarSchoenfliesFamilyData (fun t => C t l) 0 1)
      (GN : (l : Fin 2) → PlanarFamilyGraphChart (PN l)),
      (∀ l : Fin 2,
        ((GN l).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside =
          (B l).inside ∧
        ((GN l).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
          (B l).closedRegion) ∧
      ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
        ((GN 0).fiberBallNeighborhood t ht).closedRegion ⊆
          ((GN 1).fiberBallNeighborhood t ht).inside := by
  classical
  let PN : (l : Fin 2) → PlanarSchoenfliesFamilyData (fun t => C t l) 0 1 :=
    fun l => Classical.choice
      (hP.2 0 1 (fun t => C t l) zero_lt_one (hSmooth l)
        (fun t ht => hEmbedding t ht l))
  let GN : (l : Fin 2) → PlanarFamilyGraphChart (PN l) :=
    fun l => Classical.choice ((PN l).nonempty_graphChart zero_lt_one)
  have hInitialRegions (l : Fin 2) :
      ((GN l).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside = (B l).inside ∧
      ((GN l).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
        (B l).closedRegion :=
    ⟨(GN l).fiber_inside_eq 0 ⟨le_rfl, zero_le_one⟩ (B l) (hBoundary l),
      (GN l).fiber_closedRegion_eq 0 ⟨le_rfl, zero_le_one⟩ (B l) (hBoundary l)⟩
  refine ⟨PN, GN, hInitialRegions, ?_⟩
  apply planarFamilyGraphCharts_preserve_nesting C PN GN 0 1 hDisjoint
  rw [(hInitialRegions 0).2, (hInitialRegions 1).1]
  exact hNested

end PoincareConjecture.M25.Topology3D

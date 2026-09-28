import PoincareConjecture.Proofs.M76.Mathlib.SmallConvexHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexCone










set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {ι : Type*} [Finite ι]






theorem exists_small_closedStar_halfspace_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzeroK : (0 : E) ∈ K.vertices) {U : Set E} (hU : IsOpen U)
    (hzeroU : (0 : E) ∈ U) (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E) (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ)
      (J : SimplicialComplex ℝ E),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧ C ⊆ U ∧
      Disjoint C (K.link 0).space ∧
      K.space ∩ C = (K.closedStar 0).space ∩ C ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C := by
  obtain ⟨η, hη, hstar⟩ := K.exists_ball_inter_space_subset_closedStar hK hzeroK
  have hlink : IsClosed (K.link 0).space :=
    ((K.link 0).isCompact_space_of_finite (finite_link_faces hK 0)).isClosed
  let V := U ∩ ball (0 : E) η ∩ (K.link 0).spaceᶜ
  have hV : IsOpen V := (hU.inter isOpen_ball).inter hlink.isOpen_compl
  have hzeroV : (0 : E) ∈ V :=
    ⟨⟨hzeroU, mem_ball_self hη⟩, K.zero_notMem_link_space⟩
  obtain ⟨C, L, J, hC, hcv, h0C, hCV, hL, hrep, hJ, hJC⟩ :=
    hV.exists_small_convex_halfspace_frontier hzeroV c
  have hlocal : K.space ∩ C = (K.closedStar 0).space ∩ C := by
    apply Subset.antisymm
    · exact fun _ hx => ⟨hstar ⟨hx.1, (hCV hx.2).1.2⟩, hx.2⟩
    · exact fun _ hx =>
        ⟨space_subset_of_le (show K.closedStar 0 ≤ K from fun _ hs => hs.1) hx.1, hx.2⟩
  exact ⟨C, L, J, hC, hcv, h0C, fun _ hx => (hCV hx).1.1,
    disjoint_left.mpr (fun _ hx hy => (hCV hx).2 hy), hlocal,
    hL, hrep, hJ, hJC⟩

end Geometry.SimplicialComplex

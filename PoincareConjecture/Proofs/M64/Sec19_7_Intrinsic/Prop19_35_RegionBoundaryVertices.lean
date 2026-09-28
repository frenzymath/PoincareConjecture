import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionEuler

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

section Faces

variable {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
  (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
  (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
  (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
  (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
    affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
  (hinter : ∀ i j, i ≠ j →
    (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})

include hsource hboundary hinter

theorem m64Intrinsic_one_face_edge_endpoints_frontier
    (e : FaceBoundaryEdge face)
    (he : Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 1) :
    (Euler.coordinateEdgeEnds face F b e).1.1 ∈ frontier (⋃ i, (face i).carrier) ∧
      (Euler.coordinateEdgeEnds face F b e).2.1 ∈ frontier (⋃ i, (face i).carrier) := by
  have hsub := (Nat.card_eq_one_iff_unique.mp he).1
  have hrep : faceBoundaryIndex face e.out.1 e.out.2 = e := Quotient.out_eq e
  have hunpaired (q : I × Fin 3)
      (hq : faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face e.out.1 e.out.2) :
      q = e.out := congrArg Subtype.val (hsub.elim
        (⟨q, hq.trans hrep⟩ : {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e})
        ⟨e.out, hrep⟩)
  have h := m64Intrinsic_unpaired_side_subset_region_frontier face F b hsource hboundary
    hinter e.out hunpaired
  constructor
  · have hzero := h (mem_image_of_mem _ (by simp : (0 : ℝ) ∈ Icc 0 1))
    simpa [Euler.coordinateEdgeEnds, Euler.coordinateCorner, hboundary,
      Function.comp_apply, affineChartSegment] using hzero
  · have hone := h (mem_image_of_mem _ (by simp : (1 : ℝ) ∈ Icc 0 1))
    simpa [Euler.coordinateEdgeEnds, Euler.coordinateCorner, hboundary,
      Function.comp_apply, affineChartSegment] using hone

theorem m64Intrinsic_interior_vertex_boundary_degree_zero
    (v : Euler.CoordinateVertex F b)
    (hv : v.1 ∈ interior (⋃ i, (face i).carrier)) :
    Nat.card {e : {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
      faceBoundaryIndex face p.1 p.2 = e} = 1} //
      (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
        (Euler.coordinateEdgeEnds face F b e.1).2 = v} = 0 := by
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨?_⟩
  rintro ⟨e, he⟩
  have hends := m64Intrinsic_one_face_edge_endpoints_frontier face F b hsource
    hboundary hinter e.1 e.2
  rcases he with he | he
  · exact (he ▸ hends.1).2 hv
  · exact (he ▸ hends.2).2 hv

end Faces
end PoincareConjecture

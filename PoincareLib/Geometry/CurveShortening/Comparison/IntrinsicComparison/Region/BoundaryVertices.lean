import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Region.Euler

/-!
# Boundary vertices in the regional Euler formula

An edge with one incident face has both actual endpoints on the regional
frontier. Interior vertices therefore have boundary degree zero.
These are geometric inputs to the signed
turning formula of Morgan--Tian Lemma 19.45, printed p. 474.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

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

/-- The two canonical geometric endpoints of a one-face edge both lie on the actual regional
frontier. The unique slot is derived from its finite fiber cardinality rather than supplied
separately. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, including the
Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional construction is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`,
Mathematical Checks. -/
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

/-- A vertex inside the actual region has no incident one-face edge. Thus its
boundary-degree term in the regional Euler formula is zero. Source: Morgan--Tian Proposition
19.35, printed pp. 467-481, including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the
explicit regional construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
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
end PoincareMT

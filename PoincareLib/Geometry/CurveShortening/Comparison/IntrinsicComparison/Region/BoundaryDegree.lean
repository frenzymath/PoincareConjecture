import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Exposed.EdgeVertices
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Return.TraceIncidence

/-!
# The exact boundary degree of the return region

Canonical one-face edges form the actual simple-loop trace. Their
two-edge incidence therefore gives degree two at every boundary vertex
in the regional Euler formula. No graph degree or ordering is assumed.

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

/-- Every actual boundary vertex of the compatible return-region triangulation has exactly
two incident one-face geometric edges. Source: Morgan--Tian Proposition 19.35, printed pp.
467-481, including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional
construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
theorem m64Intrinsic_return_region_boundary_vertex_degree_two
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hgamma : ContinuousOn gamma (Icc 0 T)) (hend : gamma 0 = gamma T)
    (hginj : InjOn gamma (Ico 0 T))
    (htrace : frontier (⋃ i, (face i).carrier) = gamma '' Icc 0 T)
    (v : Euler.CoordinateVertex F b) (hv : v.1 ∈ frontier (⋃ i, (face i).carrier)) :
    Nat.card {e : {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
      faceBoundaryIndex face p.1 p.2 = e} = 1} //
      (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
        (Euler.coordinateEdgeEnds face F b e.1).2 = v} = 2 := by
  classical
  let E := {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
    faceBoundaryIndex face p.1 p.2 = e} = 1}
  let f (e : E) := (faceBoundaryEdge face e.1).map
  have hcover : (⋃ e : E, f e '' Icc (0 : ℝ) 1) = gamma '' Icc 0 T :=
    (m64Intrinsic_region_frontier_eq_one_face_edges face F b hsource hcarrier
      hboundary hinter hfront).symm.trans htrace
  have hinj (i : I) (k : Fin 3) : InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) :=
    m64Intrinsic_coordinate_boundary_injective face F b hsource hboundary i k
  have hmeet (e d : E) (hed : e ≠ d) :
      f e '' Icc (0 : ℝ) 1 ∩ f d '' Icc (0 : ℝ) 1 ⊆ {f e 0, f e 1} := by
    apply Euler.coordinate_cover_edge_meet face F b hsource hboundary hinj hinter
      e.1.out.1 d.1.out.1 e.1.out.2 d.1.out.2
    intro h
    apply hed
    apply Subtype.ext
    exact (Quotient.out_eq e.1).symm.trans
      (((faceBoundaryIndex_eq_iff face _ _ _ _).mpr h).trans (Quotient.out_eq d.1))
  have hvertex (e : E) : v.1 ∈ f e '' Icc (0 : ℝ) 1 ↔ v.1 = f e 0 ∨ v.1 = f e 1 :=
    m64Intrinsic_vertex_on_one_face_edge_iff_endpoint face F b hsource hcarrier
      hboundary hinter e.1 e.2 v
  have hp : ∃ e : E, v.1 = f e 0 ∨ v.1 = f e 1 := by
    have hvmem : v.1 ∈ ⋃ e : E, f e '' Icc (0 : ℝ) 1 := by
      rw [hcover, ← htrace]
      exact hv
    obtain ⟨e, he⟩ := mem_iUnion.mp hvmem
    exact ⟨e, (hvertex e).mp he⟩
  obtain ⟨e, d, hed, hmembers⟩ := m64Intrinsic_return_trace_exactly_two_arcs
    hT hgamma hend hginj f
    (fun e => (faceBoundaryEdge face e.1).smooth.continuousOn)
    (fun e => hinj e.1.out.1 e.1.out.2) hmeet hcover hp
  let P (e : E) := (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
    (Euler.coordinateEdgeEnds face F b e.1).2 = v
  have hleft (e : E) : (Euler.coordinateEdgeEnds face F b e.1).1.1 = f e 0 := by
    simp [Euler.coordinateEdgeEnds, Euler.coordinateCorner, f, faceBoundaryEdge,
      hboundary, affineChartSegment]
  have hright (e : E) : (Euler.coordinateEdgeEnds face F b e.1).2.1 = f e 1 := by
    simp [Euler.coordinateEdgeEnds, Euler.coordinateCorner, f, faceBoundaryEdge,
      hboundary, affineChartSegment]
  have hP (e : E) : P e ↔ v.1 ∈ f e '' Icc (0 : ℝ) 1 := by
    rw [hvertex]
    constructor
    · rintro (h | h)
      · exact Or.inl ((congrArg Subtype.val h).symm.trans (hleft e))
      · exact Or.inr ((congrArg Subtype.val h).symm.trans (hright e))
    · rintro (h | h)
      · exact Or.inl (Subtype.ext ((hleft e).trans h.symm))
      · exact Or.inr (Subtype.ext ((hright e).trans h.symm))
  have hPe : P e := (hP e).mpr ((hmembers e).mpr (Or.inl rfl))
  have hPd : P d := (hP d).mpr ((hmembers d).mpr (Or.inr rfl))
  let a : {e : E // P e} := ⟨e, hPe⟩
  let z : {e : E // P e} := ⟨d, hPd⟩
  let _ := Fintype.ofFinite {e : E // P e}
  have haz : a ≠ z := fun h => hed (congrArg Subtype.val h)
  have huniv : (Finset.univ : Finset {e : E // P e}) = {a, z} := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases (hmembers c.1).mp ((hP c.1).mp c.2) with hc | hc
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr (Subtype.ext hc)
  change Nat.card {e : E // P e} = 2
  rw [Nat.card_eq_fintype_card, Fintype.card, huniv, Finset.card_pair haz]

end PoincareMT

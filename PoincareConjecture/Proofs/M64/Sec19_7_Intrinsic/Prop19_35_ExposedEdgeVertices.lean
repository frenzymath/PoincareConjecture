import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryVertices













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
  (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
  (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
    affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
  (hinter : ∀ i j, i ≠ j →
    (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})

include hsource hboundary in
omit [Finite I] in




theorem m64Intrinsic_coordinate_boundary_injective (i : I) (k : Fin 3) :
    InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hsource' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)) r ∈ (F i).source :=
    hsource i (Euler.coordinate_edge_subset_hull (b i) k
      (Euler.affineChartSegment_image _ _ ▸ mem_image_of_mem _ hr))
  rw [hboundary] at hst
  have h := (F i).injOn (hsource' s hs) (hsource' t ht) hst
  simp only [Euler.affineChartSegment_eq_lineMap] at h
  apply AffineMap.lineMap_injective ℝ ?_ h
  intro heq
  have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective ((b i).ind.injective heq)
  norm_num at h01

include hsource hcarrier hboundary hinter in





theorem m64Intrinsic_region_frontier_eq_one_face_edges
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier) :
    frontier (⋃ i, (face i).carrier) =
      ⋃ e : {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
        faceBoundaryIndex face p.1 p.2 = e} = 1},
        (faceBoundaryEdge face e.1).map '' Icc (0 : ℝ) 1 := by
  rw [m64Intrinsic_region_frontier_eq_unpaired_sides face F b hsource hcarrier
    hboundary hinter hfront]
  apply Subset.antisymm
  · rintro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    let e := faceBoundaryIndex face p.1.1 p.1.2
    have he : Nat.card {q : I × Fin 3 // faceBoundaryIndex face q.1 q.2 = e} = 1 := by
      apply Nat.card_eq_one_iff_unique.mpr
      refine ⟨⟨?_⟩, ⟨⟨p.1, rfl⟩⟩⟩
      intro q r
      exact Subtype.ext ((p.2 q.1 q.2).trans (p.2 r.1 r.2).symm)
    apply mem_iUnion.mpr
    refine ⟨⟨e, he⟩, ?_⟩
    simpa only [e, faceBoundaryEdge_image] using hp
  · rintro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    have hsub := (Nat.card_eq_one_iff_unique.mp e.2).1
    have hrep : faceBoundaryIndex face e.1.out.1 e.1.out.2 = e.1 := Quotient.out_eq e.1
    have hunpaired : ∀ q : I × Fin 3,
        faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face e.1.out.1 e.1.out.2 →
          q = e.1.out := by
      intro q hq
      exact congrArg Subtype.val (hsub.elim
        (⟨q, hq.trans hrep⟩ : {q : I × Fin 3 // faceBoundaryIndex face q.1 q.2 = e.1})
        ⟨e.1.out, hrep⟩)
    exact mem_iUnion.mpr ⟨⟨e.1.out, hunpaired⟩, he⟩

include hsource hcarrier hboundary hinter in
omit [Finite I] in





theorem m64Intrinsic_vertex_on_one_face_edge_iff_endpoint
    (e : FaceBoundaryEdge face)
    (he : Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 1)
    (v : Euler.CoordinateVertex F b) :
    v.1 ∈ (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 ↔
      v.1 = (faceBoundaryEdge face e).map 0 ∨ v.1 = (faceBoundaryEdge face e).map 1 := by
  constructor
  · rintro ⟨t, ht, htv⟩
    obtain ⟨⟨i, k⟩, hik⟩ := v.2
    have hsub := (Nat.card_eq_one_iff_unique.mp he).1
    have hrep : faceBoundaryIndex face e.out.1 e.out.2 = e := Quotient.out_eq e
    have hpoint (w : Fin 3) (hw : v.1 = F e.out.1 (b e.out.1 w)) : t = 0 ∨ t = 1 := by
      apply Euler.coordinate_vertex_on_edge (F e.out.1) (b e.out.1)
        (hsource e.out.1) e.out.2 w ht
      change ((F e.out.1) ∘ affineChartSegment
        (b e.out.1 (e.out.2.succAbove 0)) (b e.out.1 (e.out.2.succAbove 1))) t = _
      rw [← hboundary]
      exact htv.trans hw
    have hend : t = 0 ∨ t = 1 := by
      by_cases hi : e.out.1 = i
      · exact hpoint k (by simpa only [hi] using hik.symm)
      have hvi : v.1 ∈ (face i).carrier := by
        rw [hcarrier]
        exact ⟨b i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
      have hve : v.1 ∈ (face e.out.1).carrier :=
        (face e.out.1).isClosed_carrier.frontier_subset
          ((face e.out.1).boundary_image_subset_frontier e.out.2 ⟨t, ht, htv⟩)
      rcases hinter e.out.1 i hi with ⟨l, j, hl, hj⟩ | ⟨w, hw⟩
      · by_cases hl' : l = e.out.2
        · subst l
          have hij : faceBoundaryIndex face i j = e :=
            ((faceBoundaryIndex_eq_iff face _ _ _ _).mpr hj.symm).trans hrep
          have heq := congrArg Subtype.val (hsub.elim
            (⟨(i, j), hij⟩ : {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e})
            ⟨e.out, hrep⟩)
          exact False.elim (hi (congrArg Prod.fst heq).symm)
        · have hvother : v.1 ∈ ((face e.out.1).boundary l).map '' Icc (0 : ℝ) 1 :=
            hl ▸ ⟨hve, hvi⟩
          have hvown : v.1 ∈ ((face e.out.1).boundary e.out.2).map '' Icc (0 : ℝ) 1 :=
            ⟨t, ht, htv⟩
          rw [hboundary] at hvown hvother
          rcases Euler.coordinate_distinct_edges (F e.out.1) (b e.out.1)
            (hsource e.out.1) e.out.2 l (Ne.symm hl') ⟨hvown, hvother⟩ with h | h
          · exact hpoint _ h
          · exact hpoint _ h
      · exact hpoint w (hw ⟨hve, hvi⟩)
    rcases hend with rfl | rfl
    · exact Or.inl htv.symm
    · exact Or.inr htv.symm
  · rintro (h | h)
    · exact ⟨0, by simp, h.symm⟩
    · exact ⟨1, by simp, h.symm⟩

end Faces
end PoincareConjecture

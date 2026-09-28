import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightBoundaryContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandBoundaryContact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

theorem m64Intrinsic_refined_band_child_chord_contact
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (p : Fin B.interface.count × Bool) (c : AffineBasis (Fin 3) ℝ Plane)
    (hchild : convexHull ℝ (range c) ⊆ convexHull ℝ (range (B.faceBasis p)))
    (hone : ∃ i : Fin 3, convexHull ℝ (range c) ∩
      frontier (convexHull ℝ (range (B.faceBasis p))) ⊆
        affineSegment ℝ (B.faceBasis p (i.succAbove 0)) (B.faceBasis p (i.succAbove 1)))
    (hvertices : ∀ i j : Fin 3, B.faceBasis p i ∈ convexHull ℝ (range c) →
      B.faceBasis p j ∈ convexHull ℝ (range c) → i = j)
    (hcuts : ∀ right : Bool, ∃ u v : AnnulusCoordinates,
      (B.endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v)
    (G : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (d : AffineBasis (Fin 3) ℝ Plane)
    (hother : convexHull ℝ (range d) ⊆ G.source)
    (j : Fin 3) (u v : AnnulusCoordinates)
    (hchord : G '' affineSegment ℝ (d (j.succAbove 0)) (d (j.succAbove 1)) = segment ℝ u v)
    (houter : B.carrier ∩ (G '' convexHull ℝ (range d)) ⊆ B.leftCut ∪ B.rightCut)
    (hcap : B.carrier ∩ (G '' convexHull ℝ (range d)) ⊆
      G '' affineSegment ℝ (d (j.succAbove 0)) (d (j.succAbove 1))) :
    CoordinateTriangleBoundaryIntersection (B.faceCoordinates p) G c d := by
  classical
  let X := (B.faceCoordinates p '' convexHull ℝ (range c)) ∩
    (G '' convexHull ℝ (range d))
  have hsource := B.face_triangle_subset_source p
  have hcin := hchild.trans hsource
  have hparent : B.faceCoordinates p '' convexHull ℝ (range c) ⊆ (B.face p).carrier := by
    rw [B.face_carrier_eq_coordinates]
    exact image_mono hchild
  have hband : (B.face p).carrier ⊆ B.carrier :=
    fun _ hx => mem_iUnion.mpr ⟨p, hx⟩
  have hxband {x : AnnulusCoordinates} (hx : x ∈ X) : x ∈ B.carrier :=
    hband (hparent hx.1)
  have hfront {x : AnnulusCoordinates} (hx : x ∈ X) : x ∈ frontier (B.face p).carrier := by
    have houterx := houter ⟨hxband hx, hx.2⟩
    have hfrontB : x ∈ frontier B.carrier := B.outer_boundaries_subset_frontier
      (by
        rcases houterx with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h)
    exact ⟨subset_closure (hparent hx.1), fun hi => hfrontB.2 (interior_mono hband hi)⟩
  have hsourcefront {x : AnnulusCoordinates} (hx : x ∈ X)
      {z : Plane} (hz : z ∈ convexHull ℝ (range c)) (hzx : B.faceCoordinates p z = x) :
      z ∈ frontier (convexHull ℝ (range (B.faceBasis p))) := by
    have h := hfront hx
    rw [B.face_frontier_eq_coordinates] at h
    obtain ⟨w, hw, hwx⟩ := h
    have hwsource : w ∈ (B.faceCoordinates p).source :=
      hsource (((finite_range (B.faceBasis p)).isCompact_convexHull ℝ).isClosed.frontier_subset hw)
    exact (B.faceCoordinates p).injOn (hcin hz) hwsource (hzx.trans hwx.symm) ▸ hw
  obtain ⟨i, hi⟩ := hone
  have hleft : X ⊆ B.faceCoordinates p ''
      affineSegment ℝ (B.faceBasis p (i.succAbove 0)) (B.faceBasis p (i.succAbove 1)) := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    exact ⟨z, hi ⟨hz, hsourcefront hx hz hzx⟩, hzx⟩
  have hright : X ⊆ G '' affineSegment ℝ (d (j.succAbove 0)) (d (j.succAbove 1)) :=
    fun _ hx => hcap ⟨hxband hx, hx.2⟩
  by_cases hselected : ∃ right : Bool,
      p = (if right then (B.lastCell, false) else (B.firstCell, true)) ∧
        i = (if right then 0 else 2)
  · obtain ⟨right, hp, hi⟩ := hselected
    obtain ⟨s, t, hcut⟩ := hcuts right
    have hedge : B.faceCoordinates p ''
        affineSegment ℝ (B.faceBasis p (i.succAbove 0)) (B.faceBasis p (i.succAbove 1)) =
          (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by
      rw [← Euler.affineChartSegment_image, ← image_comp, ← B.face_boundary_image]
      subst p
      subst i
      cases right <;> rfl
    exact m64Intrinsic_child_straight_boundary_contact (B.faceCoordinates p) G
      (B.faceBasis p) c d hsource hchild hother i j s t u v
      (hedge.trans hcut).subset hchord hleft hright
  · have hcorner : X ⊆ range (fun k : Fin 3 => B.faceCoordinates p (B.faceBasis p k)) := by
      intro x hx
      apply m64Intrinsic_band_side_outer_contact_corners B p i
        (fun right h => hselected ⟨right, h⟩)
      refine ⟨?_, houter ⟨hxband hx, hx.2⟩⟩
      rw [B.face_boundary_image, image_comp, Euler.affineChartSegment_image]
      exact hleft hx
    have hpoint : X.Subsingleton := by
      intro x hx y hy
      obtain ⟨k, hk⟩ := hcorner hx
      obtain ⟨l, hl⟩ := hcorner hy
      have hmem {z : AnnulusCoordinates} (hz : z ∈ X) (k : Fin 3)
          (hk : B.faceCoordinates p (B.faceBasis p k) = z) :
          B.faceBasis p k ∈ convexHull ℝ (range c) := by
        obtain ⟨w, hw, hwz⟩ := hz.1
        have he := (B.faceCoordinates p).injOn
          (hsource (subset_convexHull ℝ _ (mem_range_self k))) (hcin hw) (hk.trans hwz.symm)
        exact he.symm ▸ hw
      have hkl := hvertices k l (hmem hx k hk) (hmem hy l hl)
      exact hk.symm.trans (hkl ▸ hl)
    by_cases hne : X.Nonempty
    · obtain ⟨x, hx⟩ := hne
      apply CoordinateTriangleBoundaryIntersection.point x
      · obtain ⟨z, hz, hzx⟩ := hx.1
        refine ⟨z, ⟨subset_closure hz, ?_⟩, hzx⟩
        intro hzi
        exact (hsourcefront hx hz hzx).2 (interior_mono hchild hzi)
      · exact image_mono (Euler.coordinate_edge_subset_frontier d j) (hright hx)
      · intro y hy
        exact mem_singleton_iff.mpr (hpoint hy hx)
    · exact CoordinateTriangleBoundaryIntersection.disjoint
        (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne))

theorem m64Intrinsic_refine_band_faces_to_chord_family
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (hcuts : ∀ right : Bool, ∃ u v : AnnulusCoordinates,
      (B.endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v)
    {J : Type*} (G : J → OpenPartialHomeomorph Plane AnnulusCoordinates)
    (d : J → AffineBasis (Fin 3) ℝ Plane)
    (hother : ∀ j, convexHull ℝ (range (d j)) ⊆ (G j).source)
    (k : J → Fin 3) (u v : J → AnnulusCoordinates)
    (hchord : ∀ j, G j '' affineSegment ℝ (d j ((k j).succAbove 0))
      (d j ((k j).succAbove 1)) = segment ℝ (u j) (v j))
    (houter : ∀ j, B.carrier ∩ (G j '' convexHull ℝ (range (d j))) ⊆
      B.leftCut ∪ B.rightCut)
    (hcap : ∀ j, B.carrier ∩ (G j '' convexHull ℝ (range (d j))) ⊆
      G j '' affineSegment ℝ (d j ((k j).succAbove 0)) (d j ((k j).succAbove 1))) :
    ∃ M : (Fin B.interface.count × Bool) → TriangleMesh,
      (∀ p, (M p).toPlaneComplex.support = convexHull ℝ (range (B.faceBasis p))) ∧
      (∀ p, (M p).toPlaneComplex.Subdivides
        (TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).toPlaneComplex) ∧
      ∀ p (t : (M p).Triangle) j,
        CoordinateTriangleBoundaryIntersection (B.faceCoordinates p) (G j)
          (meshTriangleBasis (M p) t) (d j) := by
  classical
  choose M hsupport hsubdiv hone hvertices using fun p : Fin B.interface.count × Bool =>
    m64Intrinsic_exists_parent_boundary_refinement (B.faceBasis p)
  refine ⟨M, hsupport, hsubdiv, ?_⟩
  intro p t j
  have hcarrier : (M p).triangleCarrier t.1 =
      convexHull ℝ (range (meshTriangleBasis (M p) t)) := by
    rw [TriangleMesh.triangleCarrier, range_meshTriangleBasis]
  apply m64Intrinsic_refined_band_child_chord_contact B p (meshTriangleBasis (M p) t)
    ?_ ?_ ?_ hcuts (G j) (d j) (hother j) (k j) (u j) (v j)
    (hchord j) (houter j) (hcap j)
  · rw [← hsupport p]
    exact meshTriangleBasis_subset_support (M p) t
  · simpa only [hcarrier] using hone p t
  · simpa only [hcarrier] using hvertices p t

end PoincareConjecture

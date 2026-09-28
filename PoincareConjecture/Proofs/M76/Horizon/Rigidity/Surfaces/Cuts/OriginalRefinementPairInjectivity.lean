import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.CutMapOrientationTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutRectangle
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

local notation "Sq" => PeriodicSquare.squareCarrier 1

theorem marked_rectangle_interior_off_rim
    (C : Sq ≃ₜ A.carrier)
    (hbottom : ∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0)
    (htop : ∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1)
    (hleft : ∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0)
    (hright : ∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1)
    {x : ℝ × ℝ} (hx : x ∈ interior Sq) :
    (C ⟨x,interior_subset hx⟩).val ∉ A.rim := by
  have hx' : x ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    simpa only [PeriodicSquare.squareCarrier,interior_prod_eq,interior_Icc] using hx
  intro hr
  rw [← A.longBoundaryArcs_cover] at hr
  obtain ⟨i,hi⟩ := mem_iUnion.mp hr
  fin_cases i
  · exact (ne_of_gt hx'.2.1) ((hbottom _).mp hi)
  · exact (ne_of_lt hx'.1.2) ((hright _).mp hi)
  · exact (ne_of_lt hx'.2.2) ((htop _).mp hi)
  · exact (ne_of_gt hx'.1.1) ((hleft _).mp hi)

include hbound



theorem sourceMap_comp_injOn_triangle_pair
    (C : Sq ≃ₜ A.carrier)
    (hbottom : ∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0)
    (htop : ∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1)
    (hleft : ∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0)
    (hright : ∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hspace : L.space = Sq)
    (f : (ℝ × ℝ) → ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    (hvalue : ∀ x : Sq, (C x).val = f x)
    (hf : L.AffineOnFaces f)
    (s t u : Finset (ℝ × ℝ)) (hs2 : s.card = 2)
    (ht : t ∈ L.faces) (hu : u ∈ L.faces) (ht3 : t.card = 3) (hu3 : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (hne : t ≠ u) :
    InjOn (A.sourceMap ∘ f) (convexHull ℝ (t : Set (ℝ × ℝ)) ∪
      convexHull ℝ (u : Set (ℝ × ℝ))) := by
  have hsne : (s : Set (ℝ × ℝ)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by intro he; simp [he] at hs2)
  obtain ⟨c,hc⟩ := hsne.convexHull.intrinsicInterior (convex_convexHull ℝ _)
  have hcL : c ∈ interior L.space :=
    L.mem_interior_space_of_paired_facet (by simpa using hs2) ht hu
      (by simpa using ht3) (by simpa using hu3) hst hsu hne hc
  have hcSq : c ∈ interior Sq := hspace ▸ hcL
  have hmap : MapsTo f L.space A.carrier := by
    intro x hx
    rw [← hvalue ⟨x,hspace ▸ hx⟩]
    exact (C ⟨x,hspace ▸ hx⟩).property
  have hfi : InjOn f L.space := by
    intro x hx y hy he
    have he' : C ⟨x,hspace ▸ hx⟩ = C ⟨y,hspace ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hvalue] using he
    exact congrArg Subtype.val (C.injective he')
  have hfc : f c ∈ A.carrier \ A.rim := by
    rw [← hvalue ⟨c,interior_subset hcSq⟩]
    exact ⟨(C ⟨c,interior_subset hcSq⟩).property,
      A.marked_rectangle_interior_off_rim C hbottom htop hleft hright hcSq⟩
  have hi := A.sourceMap_comp_injOn_closedFaceStar hbound L f hf hfi hmap s hfc
    (intrinsicInterior_subset hc)
  apply hi.mono
  apply union_subset
  · apply (L.closedFaceStar s).convexHull_subset_space
    exact ⟨ht,by simpa only [Finset.union_eq_right.mpr hst] using ht⟩
  · apply (L.closedFaceStar s).convexHull_subset_space
    exact ⟨hu,by simpa only [Finset.union_eq_right.mpr hsu] using hu⟩

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

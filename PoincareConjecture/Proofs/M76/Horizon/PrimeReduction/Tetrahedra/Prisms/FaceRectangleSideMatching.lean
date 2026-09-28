import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalFaceRectangleData
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.NeighborRectangleSide










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s u : Finset E}

def side (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) : Set E :=
  D.edge k b '' Icc (D.lo k b) (D.hi k b)

def openSide (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) : Set E :=
  D.edge k b '' Ioo (D.lo k b) (D.hi k b)

theorem openSide_subset_side (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    D.openSide k b ⊆ D.side k b := image_mono Ioo_subset_Icc_self

theorem side_subset_carrier (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    D.side k b ⊆ D.carrier k := by
  intro x hx
  apply (D.boundaryContact k).symm.subset
    (show x ∈ D.side k false ∪ D.side k true from ?_) |>.1
  cases b
  · exact Or.inl hx
  · exact Or.inr hx

theorem side_subset_frontier (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    D.side k b ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  intro x hx
  apply (D.boundaryContact k).symm.subset
    (show x ∈ D.side k false ∪ D.side k true from ?_) |>.2
  cases b
  · exact Or.inl hx
  · exact Or.inr hx

theorem sides_disjoint (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    Disjoint (D.side k false) (D.side k true) := by
  obtain ⟨G,_,_,_,hL,hR⟩ := D.rectangle k
  refine disjoint_left.mpr ?_
  intro x hxL hxR
  let z : D.carrier k := ⟨x,D.side_subset_carrier k false hxL⟩
  have he : (G (G.symm z) : E) = x := congrArg Subtype.val (G.apply_symm_apply z)
  have h0 := (hL (G.symm z)).mp (he.symm ▸ hxL)
  have h1 := (hR (G.symm z)).mp (he.symm ▸ hxR)
  exact zero_ne_one (h0.symm.trans h1)

theorem openSide_nonempty (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    (D.openSide k b).Nonempty := by
  obtain ⟨_,_,_,_,_,_,hlt,_⟩ := D.edgeData k b
  exact (nonempty_Ioo.mpr hlt).image _

theorem side_sdiff_physical_cut (D : OriginalFaceRectangles K g S s)
    (hgi : InjOn g K.space) (hs : s ∈ K.faces) (k : D.Region) (b : Bool) :
    D.side k b \ g ⁻¹' S = D.openSide k b := by
  obtain ⟨_,_,hes,_,hlo,hhi,_,hgap,hleft,hright⟩ := D.edgeData k b
  obtain ⟨hl,hr,havoid⟩ := original_face_edge_gap_to_physical_cut K g hgi hs
    D.arcSubset D.arcPhysical (D.edge k b) hes hlo.1.le hhi.2.le hleft hright hgap
  ext x
  constructor
  · exact fun hx => mem_open_interval_image_of_noncut _ hl hr hx.1 hx.2
  · exact fun hx => ⟨D.openSide_subset_side k b hx,fun hxS => disjoint_left.mp havoid hx hxS⟩

theorem exists_unique_side_at_boundary (D : OriginalFaceRectangles K g S s)
    (hgi : InjOn g K.space) (hs : s ∈ K.faces) (k : D.Region)
    {x : E} (hx : x ∈ D.carrier k)
    (hxF : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) (hxS : g x ∉ S) :
    ∃! b : Bool, x ∈ D.openSide k b := by
  have hxU := (D.boundaryContact k).subset ⟨hx,hxF⟩
  have hclosed : ∃ b, x ∈ D.side k b := by
    rcases hxU with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hclosed
  refine ⟨b,(D.side_sdiff_physical_cut hgi hs k b).subset ⟨hb,hxS⟩,?_⟩
  intro c hc
  have hc' := D.openSide_subset_side k c hc
  cases b <;> cases c <;> try rfl
  · exact False.elim (disjoint_left.mp (D.sides_disjoint k) hb hc')
  · exact False.elim (disjoint_left.mp (D.sides_disjoint k) hc' hb)

theorem whole_sides_eq_of_open_contact
    (D : OriginalFaceRectangles K g S s) (P : OriginalFaceRectangles K g S u)
    (hgi : InjOn g K.space) (hs : s ∈ K.faces) (hu : u ∈ K.faces)
    (k : D.Region) (b : Bool) (l : P.Region) (c : Bool)
    (hmeet : (D.openSide k b ∩ P.openSide l c).Nonempty) :
    ({D.edge k b 0,D.edge k b 1} : Finset E) = {P.edge l c 0,P.edge l c 1} ∧
      D.side k b = P.side l c ∧ D.openSide k b = P.openSide l c := by
  obtain ⟨hei,heK,hes,_,hlo,hhi,_,hgap,hleft,hright⟩ := D.edgeData k b
  obtain ⟨hfi,hfK,hfu,_,plo,phi,_,pgap,pleft,pright⟩ := P.edgeData l c
  obtain ⟨hedge,hside,_⟩ := original_physical_face_edge_gaps_match K g hgi hs hu
    D.arcSubset P.arcSubset D.arcPhysical P.arcPhysical (D.edge k b) (P.edge l c)
    hei hfi heK hfK hes hfu hlo.1.le hhi.2.le plo.1.le phi.2.le
    hleft hright pleft pright hgap pgap hmeet
  refine ⟨hedge,hside,?_⟩
  rw [←D.side_sdiff_physical_cut hgi hs,←P.side_sdiff_physical_cut hgi hu]
  exact congrArg (fun A => A \ g ⁻¹' S) hside

theorem exists_unique_neighbor_at_regular_contact
    (D : OriginalFaceRectangles K g S s) (P : OriginalFaceRectangles K g S u)
    (hgi : InjOn g K.space) (hs : s ∈ K.faces) (hu : u ∈ K.faces)
    (k : D.Region) (b : Bool) {x : E} (hx : x ∈ D.openSide k b)
    (hxU : x ∈ convexHull ℝ (u : Set E) \ ⋃ i, P.arc i)
    (hxF : x ∈ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)))
    (hregular : ConnectedComponents.mk (⟨x,hxU⟩ :
      (convexHull ℝ (u : Set E) \ ⋃ i, P.arc i : Set E)) ∉ P.exceptional) :
    ∃! z : P.Region × Bool, x ∈ P.openSide z.1 z.2 ∧
      D.side k b = P.side z.1 z.2 ∧ D.openSide k b = P.openSide z.1 z.2 := by
  obtain ⟨l,hl,hlu⟩ := (P.regionLabels ⟨x,hxU⟩).mp hregular
  have hxS : g x ∉ S := fun h => hxU.2
    ((original_face_cut_mem_iff K g hgi hu P.arcSubset P.arcPhysical hxU.1).mpr h)
  obtain ⟨c,hc,hcu⟩ := P.exists_unique_side_at_boundary hgi hu l hl.1 hxF hxS
  obtain ⟨_,hside,hopen⟩ := D.whole_sides_eq_of_open_contact P hgi hs hu k b l c ⟨x,hx,hc⟩
  refine ⟨(l,c),⟨hc,hside,hopen⟩,?_⟩
  rintro ⟨l',c'⟩ ⟨hc',_,_⟩
  have hl' : l' = l := hlu l' ⟨P.side_subset_carrier l' c'
    (P.openSide_subset_side l' c' hc'),hxU.2⟩
  subst l'
  exact Prod.ext rfl (hcu c' hc')

end PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles

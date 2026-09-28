import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.CutComponentRectangleNeighbors
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {t : Finset E}

abbrev RectangleSideFlag
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1) (B : Set E) :=
  {z : Σ f : TetrahedronFace K t, (D f).Region × Bool // (D z.1).carrier z.2.1 ⊆ B}

def RectangleSideFlag.carrier
    {D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1} {B : Set E}
    (z : RectangleSideFlag D B) : Set E := (D z.1.1).side z.1.2.1 z.1.2.2

def RectangleSideFlag.switch
    {D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1} {B : Set E} :
    Equiv.Perm (RectangleSideFlag D B) where
  toFun z := ⟨⟨z.1.1,z.1.2.1,!z.1.2.2⟩,z.2⟩
  invFun z := ⟨⟨z.1.1,z.1.2.1,!z.1.2.2⟩,z.2⟩
  left_inv z := by cases z with | mk z hz => cases z with | mk f kb =>
                  cases kb with | mk k b => cases b <;> rfl
  right_inv z := by cases z with | mk z hz => cases z with | mk f kb =>
                   cases kb with | mk k b => cases b <;> rfl

theorem exists_unique_cut_component_side_partner
    (hgi : InjOn g K.space) (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional)
    (z : RectangleSideFlag D B) :
    ∃! w : RectangleSideFlag D B, w.1.1 ≠ z.1.1 ∧ w.carrier = z.carrier := by
  classical
  rcases z with ⟨⟨f,k,b⟩,hk⟩
  obtain ⟨u,l,c,huf,hl,hedge,hside,hopen⟩ :=
    exists_cut_component_rectangle_neighbor K g hgi ht ht4 D hB hcomp hregular f k b hk
  let w : RectangleSideFlag D B := ⟨⟨u,l,c⟩,hl⟩
  refine ⟨w,⟨huf,hside.symm⟩,?_⟩
  rintro ⟨⟨v,m,d⟩,hm⟩ ⟨hvf,hvside⟩
  change (D v).side m d = (D f).side k b at hvside
  have hvopen : (D v).openSide m d = (D f).openSide k b := by
    rw [←(D v).side_sdiff_physical_cut hgi v.1.2.1,
      ←(D f).side_sdiff_physical_cut hgi f.1.2.1,hvside]
  obtain ⟨x,hx⟩ := (D f).openSide_nonempty k b
  have hxv := hvopen.symm.subset hx
  obtain ⟨hvedge,_,_⟩ := (D f).whole_sides_eq_of_open_contact (D v) hgi
    f.1.2.1 v.1.2.1 k b m d ⟨x,hx,hxv⟩
  have heu : ({(D f).edge k b 0,(D f).edge k b 1} : Finset E) ⊆ u.1.1 := by
    rw [hedge]
    exact ((D u).edgeData l c).2.2.1
  have hev : ({(D f).edge k b 0,(D f).edge k b 1} : Finset E) ⊆ v.1.1 := by
    rw [hvedge]
    exact ((D v).edgeData m d).2.2.1
  obtain ⟨o,_,ho⟩ := exists_unique_other_triangle_coface
    ((D f).edgeData k b).2.2.1 f.2 ((D f).edgeData k b).2.2.2.1 f.1.2.2 ht4
  have huf' : u.1.1 ≠ f.1.1 := fun he => huf (Subtype.ext (Subtype.ext he))
  have hvf' : v.1.1 ≠ f.1.1 := fun he => hvf (Subtype.ext (Subtype.ext he))
  have hvu : v = u := Subtype.ext (Subtype.ext
    ((ho v.1.1 ⟨v.2,v.1.2.2,hev,hvf'⟩).trans
      (ho u.1.1 ⟨u.2,u.1.2.2,heu,huf'⟩).symm))
  subst v
  have hxu := hopen.subset hx
  have hxS : g x ∉ S := ((D f).side_sdiff_physical_cut hgi f.1.2.1 k b).symm.subset hx |>.2
  have hxM : x ∈ (D u).carrier l := (D u).side_subset_carrier l c
    ((D u).openSide_subset_side l c hxu)
  have hxcut : x ∉ ⋃ i, (D u).arc i := fun h => hxS
    (((D u).arcPhysical.subset (mem_image_of_mem g h)).1)
  have hxU := ((D u).componentClosure l x ⟨hxM,hxcut⟩).1
  obtain ⟨r,hr,hru⟩ := ((D u).regionLabels ⟨x,hxU⟩).mp
    (hregular u ⟨x,hxU⟩ (hl hxM))
  have hml : m = l := (hru m ⟨(D u).side_subset_carrier m d
    ((D u).openSide_subset_side m d hxv),hxcut⟩).trans (hru l ⟨hxM,hxcut⟩).symm
  subst m
  have hdc : d = c := by
    obtain ⟨e,_,heu'⟩ := (D u).exists_unique_side_at_boundary hgi u.1.2.1 l hxM
      ((D u).side_subset_frontier l c ((D u).openSide_subset_side l c hxu)) hxS
    exact (heu' d hxv).trans (heu' c hxu).symm
  subst d
  rfl

theorem exists_cut_component_side_pairing
    (hgi : InjOn g K.space) (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    ∃ p : Equiv.Perm (RectangleSideFlag D B), Function.Involutive p ∧
      (∀ z, (p z).1.1 ≠ z.1.1) ∧ (∀ z, (p z).carrier = z.carrier) := by
  classical
  choose p hp hu using exists_unique_cut_component_side_partner hgi ht ht4 D hB hcomp hregular
  have hinv : Function.Involutive p := by
    intro z
    exact (hu (p z) z ⟨(hp z).1.symm,(hp z).2.symm⟩).symm
  exact ⟨hinv.toPerm p,hinv,fun z => (hp z).1,fun z => (hp z).2⟩

theorem exists_cut_component_rectangle_successor
    (hK : K.faces.Finite) (hgi : InjOn g K.space) (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    ∃ p next : Equiv.Perm (RectangleSideFlag D B), Function.Involutive p ∧
      (∀ z, (p z).1.1 ≠ z.1.1) ∧ (∀ z, (p z).carrier = z.carrier) ∧
      next = p.trans RectangleSideFlag.switch ∧
      (∀ z, (next z).1.1 ≠ z.1.1) ∧
      ∀ z, ∃ n : ℕ, 0 < n ∧ (next : RectangleSideFlag D B → RectangleSideFlag D B)^[n] z = z ∧
        Function.Injective (fun j : Fin n => (next : RectangleSideFlag D B → RectangleSideFlag D B)^[j.val] z) := by
  classical
  let := K.finite_faceOfCard hK 3
  obtain ⟨p,hp,hface,hside⟩ := exists_cut_component_side_pairing hgi ht ht4 D hB hcomp hregular
  let next := p.trans RectangleSideFlag.switch
  refine ⟨p,next,hp,hface,hside,rfl,hface,?_⟩
  intro z
  let n := Function.minimalPeriod next z
  have hn : 0 < n := Function.minimalPeriod_pos_of_mem_periodicPts (next.injective.mem_periodicPts z)
  refine ⟨n,hn,Function.isPeriodicPt_minimalPeriod next z,?_⟩
  intro i j hij
  apply Fin.ext
  exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij

end PoincareConjecture.M76.PrismBelt

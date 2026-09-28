import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.FaceRectangleSideMatching
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_unique_other_triangle_coface
    {E : Type*} [DecidableEq E] {a s t : Finset E}
    (has : a ⊆ s) (hst : s ⊆ t) (ha : a.card = 2) (hs : s.card = 3) (ht : t.card = 4) :
    ∃! u : Finset E, u ⊆ t ∧ u.card = 3 ∧ a ⊆ u ∧ u ≠ s := by
  obtain ⟨v,w,hvw,hav,haw,hvt,hwt,hv,hw,hall⟩ :=
    exists_two_triangle_cofaces_of_tetrahedron (has.trans hst) ha ht
  rcases (hall s hst hs).mp has with rfl | rfl
  · refine ⟨w,⟨hwt,hw,haw,hvw.symm⟩,?_⟩
    intro u hu
    exact ((hall u hu.1 hu.2.1).mp hu.2.2.1).resolve_left hu.2.2.2
  · refine ⟨v,⟨hvt,hv,hav,hvw⟩,?_⟩
    intro u hu
    exact ((hall u hu.1 hu.2.1).mp hu.2.2.1).resolve_right hu.2.2.2

abbrev TetrahedronFace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (t : Finset E) := {s : K.FaceOfCard 3 // s.1 ⊆ t}

theorem exists_cut_component_rectangle_neighbor
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional)
    (f : TetrahedronFace K t) (k : (D f).Region) (b : Bool)
    (hk : (D f).carrier k ⊆ B) :
    ∃ (u : TetrahedronFace K t) (l : (D u).Region) (c : Bool),
      u ≠ f ∧ (D u).carrier l ⊆ B ∧
      ({(D f).edge k b 0,(D f).edge k b 1} : Finset E) =
        {(D u).edge l c 0,(D u).edge l c 1} ∧
      (D f).side k b = (D u).side l c ∧
      (D f).openSide k b = (D u).openSide l c := by
  classical
  obtain ⟨hei,heK,hes,he2,hlo,hhi,hlt,hgap,hleft,hright⟩ := (D f).edgeData k b
  obtain ⟨u,⟨hut,hu3,heu,huf⟩,_⟩ :=
    exists_unique_other_triangle_coface hes f.2 he2 f.1.2.2 ht4
  have huK : u ∈ K.faces := K.down_closed ht hut (Finset.card_pos.mp (by omega))
  let uf : TetrahedronFace K t := ⟨⟨u,huK,hu3⟩,hut⟩
  obtain ⟨x,hx⟩ := (D f).openSide_nonempty k b
  have hxB : x ∈ B := hk ((D f).side_subset_carrier k b
    ((D f).openSide_subset_side k b hx))
  have hxS : g x ∉ S := ((D f).side_sdiff_physical_cut hgi f.1.2.1 k b).symm.subset hx |>.2
  have hxedge : x ∈ convexHull ℝ
      (({(D f).edge k b 0,(D f).edge k b 1} : Finset E) : Set E) := by
    obtain ⟨z,hz,rfl⟩ := hx
    have h := (affine_unit_interval_image ((D f).edge k b)).subset
      (mem_image_of_mem ((D f).edge k b)
        (show z ∈ Icc (0 : ℝ) 1 from ⟨hlo.1.le.trans hz.1.le,hz.2.le.trans hhi.2.le⟩))
    simpa only [Finset.coe_insert,Finset.coe_singleton] using h
  have hxfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)) := by
    apply (K.indep huK).convexHull_subset_intrinsicFrontier ?_ hxedge
    exact Finset.ssubset_iff_subset_ne.mpr ⟨heu,fun he => by
      have hc := congrArg Finset.card he
      rw [he2,hu3] at hc
      omega⟩
  have hxface : x ∈ convexHull ℝ (u : Set E) := convexHull_mono heu hxedge
  have hxU : x ∈ convexHull ℝ (u : Set E) \ ⋃ i, (D uf).arc i :=
    ⟨hxface,fun hxT => hxS (((D uf).arcPhysical.subset (mem_image_of_mem g hxT)).1)⟩
  obtain ⟨⟨l,c⟩,⟨hxc,hside,hopen⟩,_⟩ :=
    (D f).exists_unique_neighbor_at_regular_contact (D uf) hgi f.1.2.1 huK k b
      hx hxU hxfront (hregular uf ⟨x,hxU⟩ hxB)
  have hxM : x ∈ (D uf).carrier l \ ⋃ i, (D uf).arc i :=
    ⟨(D uf).side_subset_carrier l c ((D uf).openSide_subset_side l c hxc),hxU.2⟩
  have hsub : (convexHull ℝ (u : Set E) \ ⋃ i, (D uf).arc i : Set E) ⊆
      convexHull ℝ (t : Set E) \ g ⁻¹' S := by
    intro y hy
    refine ⟨convexHull_mono hut hy.1,?_⟩
    intro hyS
    exact hy.2 ((original_face_cut_mem_iff K g hgi huK (D uf).arcSubset
      (D uf).arcPhysical hy.1).mpr hyS)
  have hMsub : (D uf).carrier l ⊆ B := by
    rw [←((D uf).componentClosure l x hxM).2]
    apply closure_minimal ?_ hB
    exact (connectedComponentIn_mono x hsub).trans
      ((hcomp x ⟨hxB,hxS⟩).subset.trans sdiff_subset)
  obtain ⟨hedge,_,_⟩ := (D f).whole_sides_eq_of_open_contact (D uf) hgi
    f.1.2.1 huK k b l c ⟨x,hx,hxc⟩
  refine ⟨uf,l,c,?_,hMsub,hedge,hside,hopen⟩
  intro he
  exact huf (congrArg (fun z : TetrahedronFace K t => z.1.1) he)

end PoincareConjecture.M76.PrismBelt

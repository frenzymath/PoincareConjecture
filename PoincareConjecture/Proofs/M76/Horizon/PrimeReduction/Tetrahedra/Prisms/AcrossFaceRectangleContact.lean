import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RectangleOriginalEdges
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.SameFaceRectangleDisjointness










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem tetrahedron_distinct_faces_inter_card
    {E : Type*} [DecidableEq E] {s u t : Finset E}
    (hst : s ⊆ t) (hut : u ⊆ t) (hs : s.card = 3) (hu : u.card = 3)
    (ht : t.card = 4) (hne : s ≠ u) : (s ∩ u).card = 2 := by
  have hproper : s ∩ u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left,fun he => hne
      (Finset.eq_of_subset_of_card_le (he ▸ Finset.inter_subset_right) (by omega))⟩
  have hlt := Finset.card_lt_card hproper
  have hle := Finset.card_le_card (Finset.union_subset hst hut)
  have hcount := Finset.card_union_add_card_inter s u
  omega

theorem across_face_rectangles_meet_in_whole_side
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι] [DecidableEq ι]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E)))
    {B R : Set E} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional)
    (f u : TetrahedronFace K t) (hfu : f ≠ u)
    (k : (D f).Region) (l : (D u).Region)
    (hk : (D f).carrier k ⊆ B) (hl : (D u).carrier l ⊆ B)
    (hmeet : ((D f).carrier k ∩ (D u).carrier l).Nonempty) :
    ∃ b c : Bool, (D f).edgeVertices k b = (D u).edgeVertices l c ∧
      (D f).carrier k ∩ (D u).carrier l = (D f).side k b ∧
      (D f).side k b = (D u).side l c := by
  classical
  let a := f.1.1 ∩ u.1.1
  have ha2 : a.card = 2 := tetrahedron_distinct_faces_inter_card f.2 u.2 f.1.2.2 u.1.2.2 ht4
    (fun he => hfu (Subtype.ext (Subtype.ext he)))
  have haK : a ∈ K.faces := K.down_closed f.1.2.1 Finset.inter_subset_left
    (Finset.card_pos.mp (by omega))
  have haf : convexHull ℝ (a : Set E) ⊆ intrinsicFrontier ℝ (convexHull ℝ (f.1.1 : Set E)) := by
    apply (K.indep f.1.2.1).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,fun he => by
      have hc := congrArg Finset.card he
      rw [ha2,f.1.2.2] at hc
      omega⟩
  have hintersection {x : E} (hx : x ∈ (D f).carrier k ∩ (D u).carrier l) :
      x ∈ convexHull ℝ (a : Set E) := by
    change x ∈ convexHull ℝ ((f.1.1 ∩ u.1.1 : Finset E) : Set E)
    rw [Finset.coe_inter,←K.convexHull_inter_convexHull f.1.2.1 u.1.2.1]
    exact ⟨(D f).carrier_subset_face k hx.1,(D u).carrier_subset_face l hx.2⟩
  obtain ⟨x,hxk,hxl⟩ := hmeet
  obtain ⟨b,⟨hxb,hba⟩,_⟩ := (D f).exists_unique_side_on_original_edge k haK ha2 hxk
    (haf (hintersection ⟨hxk,hxl⟩)) (hintersection ⟨hxk,hxl⟩)
  obtain ⟨v,m,c,hvf,hm,hedge,hside,_⟩ := exists_cut_component_rectangle_neighbor K g hgi ht ht4
    D hB.isCompact.isClosed hcomp hregular f k b hk
  have hev : (D f).edgeVertices k b ⊆ v.1.1 := by
    change ({(D f).edge k b 0,(D f).edge k b 1} : Finset E) ⊆ v.1.1
    rw [hedge]
    exact ((D v).edgeData m c).2.2.1
  have heu : (D f).edgeVertices k b ⊆ u.1.1 := hba ▸ Finset.inter_subset_right
  obtain ⟨o,_,ho⟩ := exists_unique_other_triangle_coface ((D f).edgeData k b).2.2.1
    f.2 ((D f).edgeData k b).2.2.2.1 f.1.2.2 ht4
  have hvu : v = u := Subtype.ext (Subtype.ext
    ((ho v.1.1 ⟨v.2,v.1.2.2,hev,fun he => hvf (Subtype.ext (Subtype.ext he))⟩).trans
      (ho u.1.1 ⟨u.2,u.1.2.2,heu,fun he => hfu (Subtype.ext (Subtype.ext he.symm))⟩).symm))
  subst v
  have hxm : x ∈ (D u).carrier m := (D u).side_subset_carrier m c (hside.subset hxb)
  have hml : m = l := by
    by_contra hne
    exact disjoint_left.mp (same_face_rectangles_disjoint_in_cut_ball K g hgi ht ht4 D
      cut rim hcut hsub hrim hdis hphysical hB hR hwhole u hm hl hne) hxm hxl
  subst m
  refine ⟨b,c,hedge,Subset.antisymm ?_ ?_,hside⟩
  · intro y hy
    obtain ⟨d,⟨hyd,hda⟩,_⟩ := (D f).exists_unique_side_on_original_edge k haK ha2 hy.1
      (haf (hintersection hy)) (hintersection hy)
    have hdb : d = b := (D f).edgeVertices_injective k (hda.trans hba.symm)
    exact hdb ▸ hyd
  · intro y hy
    exact ⟨(D f).side_subset_carrier k b hy,(D u).side_subset_carrier l c (hside.subset hy)⟩

end PoincareConjecture.M76.PrismBelt

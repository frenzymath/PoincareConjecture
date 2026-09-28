import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem original_equal_dimensional_face_contact_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) {s u : Finset E} (hs : s ∈ K.faces) (hu : u ∈ K.faces)
    (hcard : s.card = u.card) (hne : s ≠ u) {x : E}
    (hxs : x ∈ convexHull ℝ (s : Set E)) (hxu : x ∈ convexHull ℝ (u : Set E)) :
    x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  have hproper : s ∩ u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left,fun he => hne (Finset.eq_of_subset_of_card_le
      (he ▸ Finset.inter_subset_right) hcard.ge)⟩
  apply (K.indep hs).convexHull_subset_intrinsicFrontier hproper
  rw [Finset.coe_inter,←K.convexHull_inter_convexHull hs hu]
  exact ⟨hxs,hxu⟩

theorem original_rectangle_contact_alternative
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (z w : Σ s : K.FaceOfCard 3, (D s).Region) {x : E}
    (hxz : x ∈ (D z.1).carrier z.2) (hxw : x ∈ (D w.1).carrier w.2) (hxS : g x ∉ S) :
    z = w ∨ ∃ b c, x ∈ (D z.1).openSide z.2 b ∧ x ∈ (D w.1).openSide w.2 c ∧
      (D z.1).side z.2 b = (D w.1).side w.2 c := by
  rcases z with ⟨s,k⟩
  rcases w with ⟨u,l⟩
  dsimp only at hxz hxw ⊢
  have hxs := (D s).carrier_subset_face k hxz
  have hxu := (D u).carrier_subset_face l hxw
  have hxsCut : x ∉ ⋃ i, (D s).arc i := fun h =>
    hxS (((D s).arcPhysical.subset (mem_image_of_mem g h)).1)
  have hxuCut : x ∉ ⋃ i, (D u).arc i := fun h =>
    hxS (((D u).arcPhysical.subset (mem_image_of_mem g h)).1)
  by_cases hsu : s = u
  · subst u
    left
    have he := ((D s).componentClosure k x ⟨hxz,hxsCut⟩).2.symm.trans
      ((D s).componentClosure l x ⟨hxw,hxuCut⟩).2
    have hkl := (D s).carrierInjective he
    subst l
    rfl
  · right
    have hne : s.1 ≠ u.1 := fun h => hsu (Subtype.ext h)
    have hxFs := original_equal_dimensional_face_contact_frontier K s.2.1 u.2.1
      (s.2.2.trans u.2.2.symm) hne hxs hxu
    have hxFu := original_equal_dimensional_face_contact_frontier K u.2.1 s.2.1
      (u.2.2.trans s.2.2.symm) hne.symm hxu hxs
    obtain ⟨b,hb,_⟩ := (D s).exists_unique_side_at_boundary hgi s.2.1 k hxz hxFs hxS
    obtain ⟨c,hc,_⟩ := (D u).exists_unique_side_at_boundary hgi u.2.1 l hxw hxFu hxS
    exact ⟨b,c,hb,hc,((D s).whole_sides_eq_of_open_contact (D u) hgi
      s.2.1 u.2.1 k b l c ⟨x,hb,hc⟩).2.1⟩

theorem exists_whole_original_rectangle_at_regular_boundary
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
    {x : E} (hxB : x ∈ B) (hxF : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (hxS : g x ∉ S) :
    ∃ z : CutBallRectangle D B, x ∈ (D z.1.1).carrier z.1.2 := by
  obtain ⟨v,hv,hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces ht) x).mp hxF
  have hs3 : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
  have hs : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by omega))
  let f : TetrahedronFace K t := ⟨⟨t.erase v,hs,hs3⟩,Finset.erase_subset _ _⟩
  have hxface : x ∈ convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i :=
    ⟨hxv,fun hxcut => hxS (((D f).arcPhysical.subset (mem_image_of_mem g hxcut)).1)⟩
  obtain ⟨k,hxk,_⟩ := ((D f).regionLabels ⟨x,hxface⟩).mp (hregular f ⟨x,hxface⟩ hxB)
  have hk := original_regular_region_subset_cut_ball hgi D hB hcomp f k hxk hxB
  exact ⟨⟨⟨f,k⟩,hk⟩,hxk.1⟩

theorem exists_whole_rectangles_at_original_cut_ball_contact
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (t : Bool → Finset E) (ht : ∀ i, t i ∈ K.faces) (ht4 : ∀ i, (t i).card = 4)
    (hne : t false ≠ t true) (B : Bool → Set E) (hB : ∀ i, IsClosed (B i))
    (hsub : ∀ i, B i ⊆ convexHull ℝ (t i : Set E))
    (hcomp : ∀ i x, x ∈ B i \ g ⁻¹' S →
      connectedComponentIn (convexHull ℝ (t i : Set E) \ g ⁻¹' S) x = B i \ g ⁻¹' S)
    (hregular : ∀ i (f : TetrahedronFace K (t i))
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ j, (D f.1).arc j : Set E)),
      (x : E) ∈ B i → ConnectedComponents.mk x ∉ (D f.1).exceptional)
    {x : E} (hx : x ∈ B false ∩ B true) (hxS : g x ∉ S) :
    ∃ z : CutBallRectangle (fun f : TetrahedronFace K (t false) => D f.1) (B false),
    ∃ w : CutBallRectangle (fun f : TetrahedronFace K (t true) => D f.1) (B true),
      x ∈ (D z.1.1.1).carrier z.1.2 ∧ x ∈ (D w.1.1.1).carrier w.1.2 ∧
      ((⟨z.1.1.1,z.1.2⟩ : Σ s : K.FaceOfCard 3, (D s).Region) = ⟨w.1.1.1,w.1.2⟩ ∨
        ∃ b c, x ∈ (D z.1.1.1).openSide z.1.2 b ∧ x ∈ (D w.1.1.1).openSide w.1.2 c ∧
          (D z.1.1.1).side z.1.2 b = (D w.1.1.1).side w.1.2 c) := by
  have hx₀ := original_equal_dimensional_face_contact_frontier K (ht false) (ht true)
    ((ht4 false).trans (ht4 true).symm) hne (hsub false hx.1) (hsub true hx.2)
  have hx₁ := original_equal_dimensional_face_contact_frontier K (ht true) (ht false)
    ((ht4 true).trans (ht4 false).symm) hne.symm (hsub true hx.2) (hsub false hx.1)
  obtain ⟨z,hz⟩ := exists_whole_original_rectangle_at_regular_boundary K g hgi (ht false)
    (ht4 false) (fun f => D f.1) (hB false) (hcomp false) (hregular false) hx.1 hx₀ hxS
  obtain ⟨w,hw⟩ := exists_whole_original_rectangle_at_regular_boundary K g hgi (ht true)
    (ht4 true) (fun f => D f.1) (hB true) (hcomp true) (hregular true) hx.2 hx₁ hxS
  exact ⟨z,w,hz,hw,original_rectangle_contact_alternative K g hgi D
    ⟨z.1.1.1,z.1.2⟩ ⟨w.1.1.1,w.1.2⟩ hz hw hxS⟩

end PoincareConjecture.M76.PrismBelt

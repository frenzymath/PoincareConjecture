import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.AcrossFaceRectangleContact









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {t : Finset E}

def CutBallRectangle.flag
    {D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1} {B : Set E}
    (z : CutBallRectangle D B) (b : Bool) : RectangleSideFlag D B :=
  ⟨⟨z.1.1,z.1.2,b⟩,z.2⟩

def RectangleSideFlag.rectangle
    {D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1} {B : Set E}
    (z : RectangleSideFlag D B) : CutBallRectangle D B :=
  ⟨⟨z.1.1,z.1.2.1⟩,z.2⟩

theorem actual_cut_rectangle_contact_valence
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (hgi : InjOn g K.space) (ht : t ∈ K.faces) (ht4 : t.card = 4)
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
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    (∀ z : CutBallRectangle D B,
      (D z.1.1).carrier z.1.2 ∩
        (⋃ w : {w : CutBallRectangle D B // w ≠ z}, (D w.1.1.1).carrier w.1.1.2) =
      (D z.1.1).side z.1.2 false ∪ (D z.1.1).side z.1.2 true) ∧
    (∀ z w v : CutBallRectangle D B, ∀ x,
      x ∈ (D z.1.1).carrier z.1.2 → x ∈ (D w.1.1).carrier w.1.2 →
      x ∈ (D v.1.1).carrier v.1.2 → z = w ∨ z = v ∨ w = v) := by
  classical
  let M (z : CutBallRectangle D B) := (D z.1.1).carrier z.1.2
  have hface (z w : CutBallRectangle D B) (hne : z ≠ w)
      (hmeet : (M z ∩ M w).Nonempty) : z.1.1 ≠ w.1.1 := by
    rcases z with ⟨⟨f,k⟩,hk⟩
    rcases w with ⟨⟨u,l⟩,hl⟩
    intro hfu
    dsimp only at hfu
    subst u
    have hkl : k ≠ l := fun he => hne (Subtype.ext (by subst l; rfl))
    obtain ⟨x,hx,hx'⟩ := hmeet
    exact disjoint_left.mp (same_face_rectangles_disjoint_in_cut_ball K g hgi ht ht4 D
      cut rim hcut hsub hrim hdis hphysical hB hR hwhole f hk hl hkl) hx hx'
  have hcontact (z w : CutBallRectangle D B) (hne : z ≠ w)
      (hmeet : (M z ∩ M w).Nonempty) :
      ∃ b c, (z.flag b).carrier = (w.flag c).carrier ∧
        M z ∩ M w = (z.flag b).carrier := by
    obtain ⟨b,c,_,hinter,hside⟩ := across_face_rectangles_meet_in_whole_side K g hgi ht ht4 D
      cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
      z.1.1 w.1.1 (hface z w hne hmeet) z.1.2 w.1.2 z.2 w.2 hmeet
    exact ⟨b,c,hside,hinter⟩
  have hpartner := exists_unique_cut_component_side_partner hgi ht ht4 D
    hB.isCompact.isClosed hcomp hregular
  constructor
  · intro z
    ext x
    constructor
    · rintro ⟨hx,hother⟩
      obtain ⟨w,hw⟩ := mem_iUnion.mp hother
      obtain ⟨b,c,_,hc⟩ := hcontact z w w.2.symm ⟨x,hx,hw⟩
      have hxb := hc.subset ⟨hx,hw⟩
      cases b
      · exact Or.inl hxb
      · exact Or.inr hxb
    · intro hx
      have hex : ∃ b, x ∈ (z.flag b).carrier := by
        rcases hx with hx | hx
        · exact ⟨false,hx⟩
        · exact ⟨true,hx⟩
      obtain ⟨b,hxb⟩ := hex
      obtain ⟨w,hw,_⟩ := hpartner (z.flag b)
      have hne : w.rectangle ≠ z := fun he => hw.1 (congrArg (fun v => v.1.1) he)
      refine ⟨(D z.1.1).side_subset_carrier z.1.2 b hxb,
        mem_iUnion.mpr ⟨⟨w.rectangle,hne⟩,?_⟩⟩
      exact (D w.1.1).side_subset_carrier w.1.2.1 w.1.2.2 (hw.2.symm.subset hxb)
  · intro z w v x hz hw hv
    by_cases hzw : z = w
    · exact Or.inl hzw
    by_cases hzv : z = v
    · exact Or.inr (Or.inl hzv)
    obtain ⟨b,c,hbc,hzwside⟩ := hcontact z w hzw ⟨x,hz,hw⟩
    obtain ⟨d,e,hde,hzvside⟩ := hcontact z v hzv ⟨x,hz,hv⟩
    have hbd : b = d := by
      have hb := hzwside.subset ⟨hz,hw⟩
      have hd := hzvside.subset ⟨hz,hv⟩
      cases b <;> cases d
      · rfl
      · exact (disjoint_left.mp ((D z.1.1).sides_disjoint z.1.2) hb hd).elim
      · exact (disjoint_left.mp ((D z.1.1).sides_disjoint z.1.2) hd hb).elim
      · rfl
    subst d
    obtain ⟨p,_,hp⟩ := hpartner (z.flag b)
    have heq : w.flag c = v.flag e :=
      (hp (w.flag c) ⟨(hface z w hzw ⟨x,hz,hw⟩).symm,hbc.symm⟩).trans
        (hp (v.flag e) ⟨(hface z v hzv ⟨x,hz,hv⟩).symm,hde.symm⟩).symm
    exact Or.inr (Or.inr (congrArg RectangleSideFlag.rectangle heq))

end PoincareConjecture.M76.PrismBelt

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.TwoCapLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ConstantCapSupport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.ActualCutBallTwoCaps









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_actual_belt_distinct_cap_labels
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι] [DecidableEq ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
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
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    ∃ owner : ∀ f, (D f).Arc → ι,
      (∀ f j, (D f).arc j ⊆ rim (owner f j)) ∧
      IsConnected (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2) ∧
      (∀ i, cut i ⊆ R → cut i ∩
        (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2) = rim i) ∧
      ∀ z : CutBallRectangle D B,
        owner z.1.1 ((D z.1.1).cap z.1.2 false) ≠ owner z.1.1 ((D z.1.1).cap z.1.2 true) ∧
        ∀ i, cut i ⊆ R ↔
          owner z.1.1 ((D z.1.1).cap z.1.2 false) = i ∨
          owner z.1.1 ((D z.1.1).cap z.1.2 true) = i := by
  classical
  let := K.finite_faceOfCard hK 3
  let M (z : CutBallRectangle D B) := (D z.1.1).carrier z.1.2
  let U := ⋃ z : CutBallRectangle D B, M z
  let Cap := {i // cut i ⊆ R}
  have htwo : Nat.card Cap = 2 := actual_cut_ball_has_two_caps K hK g hgi ht ht4 D
    cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
  obtain ⟨owner,howner,_,_,hcutContact⟩ := exists_original_rectangle_cut_disk_contacts K g hgi
    ht ht4 D cut rim hcut hsub hrim hdis hphysical
  have hownerCut (f : TetrahedronFace K t) (j : (D f).Arc) :
      (D f).arc j ⊆ cut (owner f j) := (howner f j).trans (hcut _).1
  have hphysical' (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) :
      x ∈ (⋃ i, cut i) ↔ g x ∈ S :=
    original_face_cut_mem_iff K g hgi ht (iUnion_subset hsub) hphysical hx
  have hcover := cut_ball_boundary_eq_disks_union_rectangles hgi ht ht4 D
    hB.isCompact.isClosed hcomp hR hphysical' hregular
  have hinc : B ∩ (⋃ i, cut i) = ⋃ i : Cap, cut i := by
    ext x
    constructor
    · rintro ⟨hxB,hxc⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hxc
      exact mem_iUnion.mpr ⟨⟨i,hwhole i ⟨x,hxB,hi⟩⟩,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨hB.1 (i.2 hi),mem_iUnion.mpr ⟨i,hi⟩⟩
  rw [hinc] at hcover
  have hU : IsClosed U := isClosed_iUnion_of_finite fun z =>
    ((D z.1.1).regionBall z.1.2).isCompact.isClosed
  have hcapContact (i : Cap) : cut i ∩ U ⊆ rim i := by
    rintro x ⟨hxi,hxU⟩
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxU
    have hx := (hcutContact z.1.1 z.1.2 i).subset ⟨hz,hxi⟩
    rcases hx with hx | hx
    · split_ifs at hx with he
      · exact he ▸ howner _ _ hx
      · exact hx.elim
    · split_ifs at hx with he
      · exact he ▸ howner _ _ hx
      · exact hx.elim
  have hfull := boundary_caps_whole_rim_contact K ht ht4 hB
    (fun i : Cap => cut i) (fun i => rim i) (fun i => hcut i) (fun i => i.2)
    (fun i j hij => hdis (fun he => hij (Subtype.ext he))) hU hcover.subset hcapContact
  have hconn : IsConnected U := isConnected_card_two_cap_boundary_remainder htwo hB
    (fun i : Cap => cut i) (fun i => rim i) (fun i => hcut i)
    (fun i j hij => hdis (fun he => hij (Subtype.ext he))) hU
    (fun i => (inter_comm _ _).trans (hfull i)) ((union_comm _ _).trans hcover.symm)
  have hpair (z w : CutBallRectangle D B) (hne : z ≠ w) (hmeet : (M z ∩ M w).Nonempty) :
      ∃ b c, (D z.1.1).side z.1.2 b = (D w.1.1).side w.1.2 c := by
    have hface : z.1.1 ≠ w.1.1 := by
      rcases z with ⟨⟨f,k⟩,hk⟩
      rcases w with ⟨⟨u,l⟩,hl⟩
      intro hfu
      dsimp only at hfu
      subst u
      have hkl : k ≠ l := fun he => hne (Subtype.ext (by subst l; rfl))
      obtain ⟨x,hx,hx'⟩ := hmeet
      exact disjoint_left.mp (same_face_rectangles_disjoint_in_cut_ball K g hgi ht ht4 D
        cut rim hcut hsub hrim hdis hphysical hB hR hwhole f hk hl hkl) hx hx'
    obtain ⟨b,c,_,_,hc⟩ := across_face_rectangles_meet_in_whole_side K g hgi ht ht4 D
      cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
      z.1.1 w.1.1 hface z.1.2 w.1.2 z.2 w.2 hmeet
    exact ⟨b,c,hc⟩
  have hsupp := original_rectangle_cut_support_constant hK D cut owner hownerCut hcutContact
    hconn.isPreconnected hpair
  have hlabels (z : CutBallRectangle D B) (i : ι) : cut i ⊆ R ↔
      owner z.1.1 ((D z.1.1).cap z.1.2 false) = i ∨
      owner z.1.1 ((D z.1.1).cap z.1.2 true) = i := by
    rw [←(D z.1.1).carrier_meets_cut_iff cut (owner z.1.1) (hownerCut z.1.1)
      (hcutContact z.1.1)]
    constructor
    · intro hi
      obtain ⟨x,hxr⟩ := (finitePL_disk_boundary_isConnected (hcut i)).nonempty
      have hx := (hfull ⟨i,hi⟩).symm.subset hxr
      obtain ⟨w,hw⟩ := mem_iUnion.mp hx.2
      exact (hsupp w z i).mp ⟨x,hw,hx.1⟩
    · rintro ⟨x,hxz,hxi⟩
      exact hwhole i ⟨x,z.2 hxz,hxi⟩
  refine ⟨owner,howner,hconn,fun i hi => hfull ⟨i,hi⟩,?_⟩
  intro z
  refine ⟨?_,hlabels z⟩
  intro heq
  have hsingle (i : Cap) : owner z.1.1 ((D z.1.1).cap z.1.2 false) = i := by
    rcases (hlabels z i).mp i.2 with hi | hi
    · exact hi
    · exact heq.trans hi
  let : Subsingleton Cap := ⟨fun i j => Subtype.ext ((hsingle i).symm.trans (hsingle j))⟩
  let := Fintype.ofFinite Cap
  have hc : Fintype.card Cap ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  rw [Nat.card_eq_fintype_card] at htwo
  omega

end PoincareConjecture.M76.PrismBelt

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ActualCutBallPrism
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalOriginalPrism

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_actual_global_cut_ball_prism
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
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional)
    (G : ∀ z : CutBallRectangle D B, Square ≃ₜ (D z.1.1).carrier z.1.2)
    (hG : ∀ z, (G z).IsFinitePL)
    (hGW : ∀ z x, (G z x : E) ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 false) ↔ (x : ℝ × ℝ).2 = 0)
    (hGZ : ∀ z x, (G z x : E) ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 true) ↔ (x : ℝ × ℝ).2 = 1)
    (hGL : ∀ z b x, (G z x : E) ∈ (D z.1.1).side z.1.2 b ↔
      (x : ℝ × ℝ).1 = if b then 1 else 0)
    (hGaffine : ∀ z b t, (G z (sidePoint b t) : E) =
      AffineMap.lineMap (G z (sidePoint b 0) : E) (G z (sidePoint b 1) : E) (t : ℝ)) :
    ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ cut i₀ ⊆ R ∧ cut i₁ ⊆ R ∧
      ∃ flip : CutBallRectangle D B → Bool,
      ∃ H : (cut i₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B, H.IsFinitePL ∧
        (∀ (x : E) (hx : x ∈ cut i₀), (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
        (∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0) ∧
        (∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) ∧
        (∀ z x, (H x : E) ∈ (D z.1.1).carrier z.1.2 ↔
          (x : E × ℝ).1 ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 (flip z))) ∧
        ∀ (z : CutBallRectangle D B) (u t : I),
          (H.symm ⟨G z ⟨(u,fiberFlip (flip z) t),u.property,(fiberFlip (flip z) t).property⟩,
            z.2 (G z _).property⟩ : E × ℝ) =
            ((G z ⟨(u,fiberFlip (flip z) 0),u.property,(fiberFlip (flip z) 0).property⟩ : E),(t : ℝ)) := by
  classical
  obtain ⟨owner,howner,hconn,hfull,hlabels⟩ := exists_actual_belt_distinct_cap_labels
    K hK g hgi ht ht4 D cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
  obtain ⟨owner',howner',_,_,hcutContact⟩ := exists_original_rectangle_cut_disk_contacts
    K g hgi ht ht4 D cut rim hcut hsub hrim hdis hphysical
  have heq : owner' = owner := by
    funext f j
    obtain ⟨x,hx,_⟩ := ((D f).arcBall j).sdiff_nonempty
    by_contra hne
    exact disjoint_left.mp (hdis hne) ((hcut _).1 (howner' f j hx))
      ((hcut _).1 (howner f j hx))
  subst owner'
  obtain ⟨x,hx⟩ := hconn.nonempty
  obtain ⟨z₀,hz₀⟩ := mem_iUnion.mp hx
  let i₀ := owner z₀.1.1 ((D z₀.1.1).cap z₀.1.2 false)
  let i₁ := owner z₀.1.1 ((D z₀.1.1).cap z₀.1.2 true)
  have hne : i₀ ≠ i₁ := (hlabels z₀).1
  have hi₀ : cut i₀ ⊆ R := ((hlabels z₀).2 i₀).mpr (Or.inl rfl)
  have hi₁ : cut i₁ ⊆ R := ((hlabels z₀).2 i₁).mpr (Or.inr rfl)
  have hphysical' (y : E) (hy : y ∈ convexHull ℝ (t : Set E)) :
      y ∈ (⋃ i, cut i) ↔ g y ∈ S :=
    original_face_cut_mem_iff K g hgi ht (iUnion_subset hsub) hphysical hy
  have hcoverR := cut_ball_boundary_eq_disks_union_rectangles hgi ht ht4 D
    hB.isCompact.isClosed hcomp hR hphysical' hregular
  have hcover : (cut i₀ ∪ cut i₁) ∪
      (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2) = R := by
    apply Subset.antisymm
    · exact union_subset (union_subset hi₀ hi₁) (fun y hy => hcoverR.symm.subset (Or.inr hy))
    · intro y hy
      rcases hcoverR.subset hy with ⟨hyB,hyC⟩ | hyU
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hyC
        rcases ((hlabels z₀).2 i).mp (hwhole i ⟨y,hyB,hi⟩) with he | he
        · refine Or.inl (Or.inl ?_)
          change y ∈ cut (owner z₀.1.1 ((D z₀.1.1).cap z₀.1.2 false))
          rwa [he]
        · refine Or.inl (Or.inr ?_)
          change y ∈ cut (owner z₀.1.1 ((D z₀.1.1).cap z₀.1.2 true))
          rwa [he]
      · exact Or.inr hyU
  have hpair (z w : CutBallRectangle D B) (hne : z ≠ w)
      (hmeet : ((D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2).Nonempty) :
      ∃ b c, (D z.1.1).side z.1.2 b = (D w.1.1).side w.1.2 c ∧
        (D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2 = (D z.1.1).side z.1.2 b := by
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
    obtain ⟨b,c,_,hinter,hside⟩ := across_face_rectangles_meet_in_whole_side K g hgi ht ht4 D
      cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
      z.1.1 w.1.1 hface z.1.2 w.1.2 z.2 w.2 hmeet
    exact ⟨b,c,hside,hinter⟩
  obtain ⟨flip,_,H,hH,hH0,hHB,hHC,hHM,hformula⟩ := exists_global_original_rectangle_prism
    hK D (three_ball_product_model hB) cut rim hcut hdis owner hcutContact i₀ i₁ hne
    (fun z => ((hlabels z).2 i₀).mp hi₀) (fun z => ((hlabels z).2 i₁).mp hi₁)
    hcover (hfull i₀ hi₀) hpair G hG hGW hGZ hGL hGaffine
  exact ⟨i₀,i₁,hne,hi₀,hi₁,flip,H,hH,hH0,hHB,hHC,hHM,hformula⟩

end PoincareConjecture.M76.PrismBelt

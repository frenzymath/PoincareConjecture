import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRectangleContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalEdgeTrimAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.TrimmedFaceCompatibility



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_rectangle_side_parameter
    {E : Type*} [TopologicalSpace E] {M L : Set E} (G : Square ≃ₜ M) (b : Bool)
    (hL : ∀ y, (G y : E) ∈ L ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    {x : E} (hxM : x ∈ M) (hxL : x ∈ L) :
    ∃ t : I, (G (sidePoint b t) : E) = x := by
  let y := G.symm ⟨x,hxM⟩
  have hy : (G y : E) = x := congrArg Subtype.val (G.apply_symm_apply ⟨x,hxM⟩)
  have hfirst := (hL y).mp (hy.symm ▸ hxL)
  let t : I := ⟨(y : ℝ × ℝ).2,y.property.2⟩
  have he : sidePoint b t = y := Subtype.ext (Prod.ext hfirst.symm rfl)
  exact ⟨t,(congrArg (fun y => (G y : E)) he).trans hy⟩

theorem original_rectangle_prism_fibers_agree
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space) {S : Set X}
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (z : Bool → Σ s : K.FaceOfCard 3, (D s).Region) (A B : Bool → Set E)
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (hMB : ∀ i, (D (z i).1).carrier (z i).2 ⊆ B i) (flip : Bool → Bool)
    (hformula : ∀ i (u t : I),
      ((H i).symm ⟨G (z i).1 (z i).2
        ⟨(u,fiberFlip (flip i) t),u.property,(fiberFlip (flip i) t).property⟩,
        hMB i (G _ _ _).property⟩ : E × ℝ) =
        ((G (z i).1 (z i).2
          ⟨(u,fiberFlip (flip i) 0),u.property,(fiberFlip (flip i) 0).property⟩ : E),(t : ℝ)))
    {x : E} (hx : ∀ i, x ∈ (D (z i).1).carrier (z i).2) (hxS : g x ∉ S) :
    (prismFiberReflection (H false) ⟨x,hMB false (hx false)⟩ : E) =
      prismFiberReflection (H true) ⟨x,hMB true (hx true)⟩ ∧
      (x ∈ prismTrim (H false) ↔ x ∈ prismTrim (H true)) := by
  rcases original_rectangle_contact_alternative K g hgi D (z false) (z true)
    (hx false) (hx true) hxS with heq | ⟨b,c,hb,hc,_⟩
  · have hMB₁ : (D (z false).1).carrier (z false).2 ⊆ B true := by
      exact (congrArg (fun w : Σ s : K.FaceOfCard 3, (D s).Region =>
        (D w.1).carrier w.2) heq).subset.trans (hMB true)
    have hGeq (y : Square) : (G (z false).1 (z false).2 y : E) = G (z true).1 (z true).2 y :=
      congrArg (fun w : Σ s : K.FaceOfCard 3, (D s).Region => (G w.1 w.2 y : E)) heq
    have hformula₁ (u t : I) :
        ((H true).symm ⟨G (z false).1 (z false).2
          ⟨(u,fiberFlip (flip true) t),u.property,(fiberFlip (flip true) t).property⟩,
          hMB₁ (G _ _ _).property⟩ : E × ℝ) =
          ((G (z false).1 (z false).2
            ⟨(u,fiberFlip (flip true) 0),u.property,(fiberFlip (flip true) 0).property⟩ : E),(t : ℝ)) := by
      have hpoint : (⟨G (z false).1 (z false).2
          ⟨(u,fiberFlip (flip true) t),u.property,(fiberFlip (flip true) t).property⟩,
          hMB₁ (G _ _ _).property⟩ : B true) =
        ⟨G (z true).1 (z true).2
          ⟨(u,fiberFlip (flip true) t),u.property,(fiberFlip (flip true) t).property⟩,
          hMB true (G _ _ _).property⟩ := Subtype.ext (hGeq _)
      rw [hpoint,hformula true,hGeq]
    let y := (G (z false).1 (z false).2).symm ⟨x,hx false⟩
    let u : I := ⟨(y : ℝ × ℝ).1,y.property.1⟩
    let t : I := ⟨(y : ℝ × ℝ).2,y.property.2⟩
    have hy : (G (z false).1 (z false).2 ⟨(u,t),u.property,t.property⟩ : E) = x :=
      congrArg Subtype.val ((G _ _).apply_symm_apply ⟨x,hx false⟩)
    have h₀ := prismFiberReflection_on_global_rectangle (H false) (G (z false).1 (z false).2)
      (hMB false) (flip false) (hformula false) u t
    have h₁ := prismFiberReflection_on_global_rectangle (H true) (G (z false).1 (z false).2)
      hMB₁ (flip true) hformula₁ u t
    refine ⟨by simpa only [hy] using h₀.trans h₁.symm,?_⟩
    have ht₀ := prismTrim_inter_global_rectangle (H false) (G (z false).1 (z false).2)
      (hMB false) (flip false) (hformula false)
    have ht₁ := prismTrim_inter_global_rectangle (H true) (G (z false).1 (z false).2)
      hMB₁ (flip true) hformula₁
    constructor
    · intro h
      exact (ht₁.symm.subset (ht₀.subset ⟨h,hx false⟩)).1
    · intro h
      exact (ht₀.symm.subset (ht₁.subset ⟨h,hx false⟩)).1
  · let side : Bool → Bool := Bool.rec b c
    have hsides (i : Bool) : x ∈ (D (z i).1).side (z i).2 (side i) := by
      cases i
      · exact (D (z false).1).openSide_subset_side _ _ hb
      · exact (D (z true).1).openSide_subset_side _ _ hc
    choose t ht using fun i => exists_rectangle_side_parameter (G (z i).1 (z i).2)
      (side i) (hL _ _ _) (hx i) (hsides i)
    have href := original_edge_contact_fiber_reflections_agree K g hgi
      (fun i => (z i).1) (fun i => D (z i).1) (fun i => (z i).2) A B H
      (fun i => G (z i).1 (z i).2) hMB flip side
      (fun i => hW _ _) (fun i => hZ _ _) (fun i => hL _ _)
      hformula (fun i => haffine _ _) (t false) (t true) ((ht false).trans (ht true).symm)
      ((ht false).symm ▸ hxS)
    have htrim := original_edge_contact_prism_trims_agree K g hgi
      (fun i => (z i).1) (fun i => D (z i).1) (fun i => (z i).2) A B H
      (fun i => G (z i).1 (z i).2) hMB flip side
      (fun i => hW _ _) (fun i => hZ _ _) (fun i => hL _ _)
      hformula (fun i => haffine _ _) (t false) (t true) ((ht false).trans (ht true).symm)
      ((ht false).symm ▸ hxS)
    exact ⟨by simpa only [ht] using href.2,by simpa only [ht] using htrim⟩

end PoincareConjecture.M76.PrismBelt

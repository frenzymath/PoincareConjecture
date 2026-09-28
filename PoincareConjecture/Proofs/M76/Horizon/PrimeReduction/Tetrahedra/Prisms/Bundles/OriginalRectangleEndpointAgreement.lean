import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRectangleFiberAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberEndpointPairs

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem original_rectangle_prism_end_pairs_agree
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
    prismTrimFiberEndPair (H false) ⟨x,hMB false (hx false)⟩ =
      prismTrimFiberEndPair (H true) ⟨x,hMB true (hx true)⟩ := by
  rcases original_rectangle_contact_alternative K g hgi D (z false) (z true)
    (hx false) (hx true) hxS with heq | ⟨b,c,hb,hc,hside⟩
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
    have h₀ := prismTrimFiberEndPair_on_global_rectangle (H false) (G (z false).1 (z false).2)
      (hMB false) (flip false) (hformula false) u t
    have h₁ := prismTrimFiberEndPair_on_global_rectangle (H true) (G (z false).1 (z false).2)
      hMB₁ (flip true) hformula₁ u t
    simpa only [hy] using h₀.trans h₁.symm
  · let side : Bool → Bool := Bool.rec b c
    have hsides (i : Bool) : x ∈ (D (z i).1).side (z i).2 (side i) := by
      cases i
      · exact (D (z false).1).openSide_subset_side _ _ hb
      · exact (D (z true).1).openSide_subset_side _ _ hc
    choose t ht using fun i => exists_rectangle_side_parameter (G (z i).1 (z i).2)
      (side i) (hL _ _ _) (hx i) (hsides i)
    have hball (i : Bool) := (D (z i).1).side_ball_from_marked_chart (z i).2
      (G (z i).1 (z i).2) (hW _ _) (hZ _ _) (hL _ _) (side i)
    have hball₀ := hball false
    change IsFinitePLBallPair ℝ ((D (z false).1).side (z false).2 b) _ at hball₀
    rw [hside] at hball₀
    have hpairs := hball₀.boundary_eq_of_same_carrier (hball true)
    have hq := quarter_pair_eq_of_endpoint_pair_eq hpairs
    have he (i : Bool) := prismTrimFiberEndPair_on_affine_side (H i) (G (z i).1 (z i).2)
      (hMB i) (flip i) (side i) (hformula i) (haffine _ _ _) (t i)
    have he' (i : Bool) :
        prismTrimFiberEndPair (H i) ⟨x,hMB i (hx i)⟩ =
          {AffineMap.lineMap (G (z i).1 (z i).2 (sidePoint (side i) 0) : E)
            (G (z i).1 (z i).2 (sidePoint (side i) 1) : E) (1/4 : ℝ),
          AffineMap.lineMap (G (z i).1 (z i).2 (sidePoint (side i) 0) : E)
            (G (z i).1 (z i).2 (sidePoint (side i) 1) : E) (3/4 : ℝ)} := by
      simpa only [ht] using he i
    exact (he' false).trans (hq.trans (he' true).symm)

end PoincareConjecture.M76.PrismBelt

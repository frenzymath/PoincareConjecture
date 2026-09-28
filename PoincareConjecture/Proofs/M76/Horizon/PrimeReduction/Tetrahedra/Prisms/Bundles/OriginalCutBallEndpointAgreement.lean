import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRectangleEndpointAgreement



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem original_cut_ball_prism_end_pairs_agree
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
    (t : Bool → Finset E) (ht : ∀ i, t i ∈ K.faces) (ht4 : ∀ i, (t i).card = 4)
    (hne : t false ≠ t true) (A B : Bool → Set E) (hB : ∀ i, IsClosed (B i))
    (hsub : ∀ i, B i ⊆ convexHull ℝ (t i : Set E))
    (hcomp : ∀ i x, x ∈ B i \ g ⁻¹' S →
      connectedComponentIn (convexHull ℝ (t i : Set E) \ g ⁻¹' S) x = B i \ g ⁻¹' S)
    (hregular : ∀ i (f : TetrahedronFace K (t i))
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ j, (D f.1).arc j : Set E)),
      (x : E) ∈ B i → ConnectedComponents.mk x ∉ (D f.1).exceptional)
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (flip : ∀ i, CutBallRectangle (fun f : TetrahedronFace K (t i) => D f.1) (B i) → Bool)
    (hformula : ∀ i (z : CutBallRectangle (fun f : TetrahedronFace K (t i) => D f.1) (B i))
      (u t : I),
      ((H i).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip i z) t),u.property,(fiberFlip (flip i z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip i z) 0),u.property,(fiberFlip (flip i z) 0).property⟩ : E),(t : ℝ)))
    {x : E} (hx : x ∈ B false ∩ B true) (hxS : g x ∉ S) :
    prismTrimFiberEndPair (H false) ⟨x,hx.1⟩ =
      prismTrimFiberEndPair (H true) ⟨x,hx.2⟩ := by
  obtain ⟨z,w,hz,hw,_⟩ := exists_whole_rectangles_at_original_cut_ball_contact
    K g hgi D t ht ht4 hne B hB hsub hcomp hregular hx hxS
  let zw : ∀ i, CutBallRectangle (fun f : TetrahedronFace K (t i) => D f.1) (B i) :=
    fun i => Bool.rec z w i
  have hmem (i : Bool) : x ∈ (D (zw i).1.1.1).carrier (zw i).1.2 := by
    cases i
    · exact hz
    · exact hw
  exact original_rectangle_prism_end_pairs_agree K g hgi D G hW hZ hL haffine
    (fun i => ⟨(zw i).1.1.1,(zw i).1.2⟩) A B H (fun i => (zw i).2)
    (fun i => flip i (zw i)) (fun i => hformula i (zw i)) hmem hxS

end PoincareConjecture.M76.PrismBelt

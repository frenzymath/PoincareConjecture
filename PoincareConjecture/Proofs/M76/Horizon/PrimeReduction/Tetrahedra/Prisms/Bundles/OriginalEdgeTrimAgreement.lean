import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalEdgeFiberAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.AffineEdgeTrimAgreement

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem original_edge_contact_prism_trims_agree
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (s : Bool → K.FaceOfCard 3)
    (D : ∀ i, OriginalFaceRectangles K g S (s i).1) (k : ∀ i, (D i).Region)
    (A B : Bool → Set E) (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (G : ∀ i, Square ≃ₜ (D i).carrier (k i))
    (hMB : ∀ i, (D i).carrier (k i) ⊆ B i) (flip side : Bool → Bool)
    (hW : ∀ i x, (G i x : E) ∈ (D i).arc ((D i).cap (k i) false) ↔ (x : ℝ × ℝ).2 = 0)
    (hZ : ∀ i x, (G i x : E) ∈ (D i).arc ((D i).cap (k i) true) ↔ (x : ℝ × ℝ).2 = 1)
    (hL : ∀ i b x, (G i x : E) ∈ (D i).side (k i) b ↔ (x : ℝ × ℝ).1 = if b then 1 else 0)
    (hformula : ∀ i (u t : I),
      ((H i).symm ⟨G i ⟨(u,fiberFlip (flip i) t),u.property,(fiberFlip (flip i) t).property⟩,
        hMB i (G i _).property⟩ : E × ℝ) =
        ((G i ⟨(u,fiberFlip (flip i) 0),u.property,(fiberFlip (flip i) 0).property⟩ : E),(t : ℝ)))
    (haffine : ∀ i b t, (G i (sidePoint b t) : E) =
      AffineMap.lineMap (G i (sidePoint b 0) : E) (G i (sidePoint b 1) : E) (t : ℝ))
    (t u : I) (hpoint : (G false (sidePoint (side false) t) : E) = G true (sidePoint (side true) u))
    (havoid : g (G false (sidePoint (side false) t)) ∉ S) :
    (G false (sidePoint (side false) t) : E) ∈ prismTrim (H false) ↔
      (G true (sidePoint (side true) u) : E) ∈ prismTrim (H true) := by
  obtain ⟨heq,_⟩ := original_edge_contact_fiber_reflections_agree K g hgi s D k A B
    H G hMB flip side hW hZ hL hformula haffine t u hpoint havoid
  exact prismTrim_agrees_on_equal_affine_sides A B
    (fun i => (D i).carrier (k i)) (fun i => (D i).side (k i) (side i))
    H G hMB flip side hformula (fun i => haffine i (side i))
    (fun i => (D i).side_ball_from_marked_chart (k i) (G i) (hW i) (hZ i) (hL i) (side i))
    heq t u hpoint

end PoincareConjecture.M76.PrismBelt

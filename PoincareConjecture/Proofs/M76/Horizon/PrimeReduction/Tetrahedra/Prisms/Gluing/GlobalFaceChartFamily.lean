import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalOriginalFaceCharts

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_face_chart_family
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1) :
    ∃ G : ∀ s k, Square ≃ₜ (D s).carrier k,
      (∀ s k, (G s k).IsFinitePL) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k false) ↔
        (x : ℝ × ℝ).2 = 0) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k true) ↔
        (x : ℝ × ℝ).2 = 1) ∧
      (∀ s k b x, (G s k x : E) ∈ (D s).side k b ↔
        (x : ℝ × ℝ).1 = if b then 1 else 0) ∧
      ∀ s k b t, (G s k (sidePoint b t) : E) =
        AffineMap.lineMap (G s k (sidePoint b 0) : E)
          (G s k (sidePoint b 1) : E) (t : ℝ) := by
  classical
  have hlocal (s : K.FaceOfCard 3) (k : (D s).Region) :
      ∃ G : Square ≃ₜ (D s).carrier k, G.IsFinitePL ∧
        (∀ x, (G x : E) ∈ (D s).arc ((D s).cap k false) ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (G x : E) ∈ (D s).arc ((D s).cap k true) ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ b x, (G x : E) ∈ (D s).side k b ↔ (x : ℝ × ℝ).1 = if b then 1 else 0) ∧
        ∀ b t, (G (sidePoint b t) : E) =
          AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ) := by
    obtain ⟨p,_,_,_,_,G,hG,hW,hZ,hL,hside⟩ :=
      (D s).exists_affine_side_fiber_chart k
    refine ⟨G,hG,hW,hZ,hL,?_⟩
    intro b t
    have h0 : (G (sidePoint b 0) : E) = p b false := by simpa using hside b 0
    have h1 : (G (sidePoint b 1) : E) = p b true := by simpa using hside b 1
    rw [h0,h1]
    exact hside b t
  choose G hG hW hZ hL hside using hlocal
  exact ⟨G,hG,hW,hZ,hL,hside⟩

end PoincareConjecture.M76.PrismBelt

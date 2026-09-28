import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedInterpolation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedEndpointAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberQuotient

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem exists_original_prism_interval_bundle
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (τ : (⋃ j, prismEnds (C j)) ≃ₜ (⋃ j, prismEnds (C j)))
    (hτ : Function.Involutive τ)
    (hτends : ∀ j (x : F.cut j.1.1 (i₀ j)) (b : Bool),
      (τ (prismEndpointLift C j x b) : E) = prismEndMap (C j) x (!b)) :
    ∃ L : C((⋃ j, prismTrim (H j)) × I, (⋃ j, prismTrim (H j))),
      (∀ j (x : prismTrim (H j)) (t : I),
        (L (⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩,t) : E) = prismFiberInterpolation (C j) x t) ∧
    ∃ W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ j, prismTrim (H j) : Set E),
      (∀ z, W (TwistedInvolutionInterval.projection τ hτ z) = prismEndpointFiberMap C L z) ∧
      (∀ p, W (TwistedInvolutionInterval.boundaryMap τ hτ p) = prismEndpointInclusion C p) ∧
      (∀ z w, prismEndpointFiberMap C L z = prismEndpointFiberMap C L w ↔
        z = w ∨ z = TwistedInvolutionInterval.deck τ w) := by
  classical
  let : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  let (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  let : Finite (RegularOriginalCutCell K g S D F.BallIndex F.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  have hagree := original_trimmed_interpolation_agrees K g hgi D G hW hZ hL haffine
    F i₀ H flip hformula C hCv havoid
  obtain ⟨L,hLvalue⟩ := exists_continuous_prism_interpolation C
    (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact) hagree
  have hpairs := original_trimmed_fiber_end_pairs_agree K g hgi D G hW hZ hL haffine
    F i₀ H flip hformula C hCv havoid
  obtain ⟨W,hWvalue,hWboundary⟩ := exists_twisted_interval_homeomorph_of_prism_interpolation C
    (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact) L hLvalue hpairs τ hτ hτends
  exact ⟨L,hLvalue,W,hWvalue,hWboundary,prismEndpointFiberMap_eq_iff C L hLvalue hpairs τ hτends⟩

end PoincareConjecture.M76.PrismBelt

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRectangleAffineFiber
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularComponentCoverage

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 600000 in
theorem original_regular_prism_affine_fiber_agrees
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
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
    (j l : RegularOriginalCutCell K g S D F.BallIndex F.ball) (x : E)
    (hj : x ∈ F.ball j.1.1 j.1.2) (hl : x ∈ F.ball l.1.1 l.1.2)
    (hxS : g x ∉ S) (r : ℝ)
    (hrj : affineFiberHeight r ((H j).symm ⟨x,hj⟩ : E × ℝ).2 ∈ I)
    (hrl : affineFiberHeight r ((H l).symm ⟨x,hl⟩ : E × ℝ).2 ∈ I) :
    (prismAffineFiberPoint (H j) ⟨x,hj⟩ r hrj : E) =
      prismAffineFiberPoint (H l) ⟨x,hl⟩ r hrl := by
  classical
  by_cases hsame : j = l
  · subst l
    rfl
  by_cases ht : j.1.1 = l.1.1
  · exfalso
    rcases j with ⟨⟨t,k⟩,hjreg⟩
    rcases l with ⟨⟨u,n⟩,hlreg⟩
    dsimp only at ht
    subst u
    have hkn : k ≠ n := fun h => hsame (Subtype.ext (by subst n; rfl))
    exact hxS ((F.mem_cut_iff_physical hgi t (F.ball_subset_tetrahedron t k hj)).mp
      ((F.intersection t hkn) ⟨hj,hl⟩))
  · let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
    let p : Bool → Cell := Bool.rec j l
    have htet : (p false).1.1.1 ≠ (p true).1.1.1 := fun h => ht (Subtype.ext h)
    obtain ⟨z,w,hz,hw,_⟩ := exists_whole_rectangles_at_original_cut_ball_contact K g hgi D
      (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
      (fun b => F.ball (p b).1.1 (p b).1.2)
      (fun b => (F.ball_pair (p b).1.1 (p b).1.2).isCompact.isClosed)
      (fun b => F.ball_subset_tetrahedron (p b).1.1 (p b).1.2)
      (fun b _ hx => F.component_physical hgi (p b).1.1 (p b).1.2 hx)
      (fun b => (p b).2) ⟨hj,hl⟩ hxS
    let zw : ∀ b, CutBallRectangle (fun f : TetrahedronFace K (p b).1.1.1 => D f.1)
        (F.ball (p b).1.1 (p b).1.2) := fun b => Bool.rec z w b
    have hmem (b : Bool) : x ∈ (D (zw b).1.1.1).carrier (zw b).1.2 := by
      cases b
      · exact hz
      · exact hw
    have hr (b : Bool) : affineFiberHeight r
        ((H (p b)).symm ⟨x,(zw b).2 (hmem b)⟩ : E × ℝ).2 ∈ I := by
      cases b
      · exact hrj
      · exact hrl
    exact original_rectangle_affine_fiber_agrees K g hgi D G hW hZ hL haffine
      (fun b => ⟨(zw b).1.1.1,(zw b).1.2⟩)
      (fun b => F.cut (p b).1.1 (i₀ (p b))) (fun b => F.ball (p b).1.1 (p b).1.2)
      (fun b => H (p b)) (fun b => (zw b).2) (fun b => flip (p b) (zw b))
      (fun b => hformula (p b) (zw b)) hmem hxS r hr

end PoincareConjecture.M76.PrismBelt

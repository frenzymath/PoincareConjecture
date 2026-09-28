import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CircleSurgeryBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ConfinedSphereBall











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



theorem exists_circle_surgery_region
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    {M : Set E}
    (hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ M ↔ z.1.2 = 0)
    (caps : Bool → Set E)
    (hcaps : ∀ c, IsFinitePLBallPair P2 (caps c)
      ((fun t => τ ((if c then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcapM : ∀ c, caps c ∩ M =
      (fun t => τ ((if c then 1/4 else -1/4,0),t)) '' Icc 0 β)
    (hdis : Disjoint (caps true) (caps false))
    {B b : Set E} (hB : IsFinitePLBallPair C3 B b)
    (htubeB : τ '' (signedTubeDiamond ×ˢ Icc 0 β) ⊆ interior B)
    (hcapsB : ∀ c, caps c ⊆ interior B) :
    let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
    let boundary := band ∪ (caps true ∪ caps false)
    IsFinitePLBallPair P2 (caps true ∪ band)
        ((fun t => τ ((-1/4,0),t)) '' Icc 0 β) ∧
      (caps true ∪ band) ∩ caps false =
        (fun t => τ ((-1/4,0),t)) '' Icc 0 β ∧
      ∃ R : Set E, IsFinitePLBallPair C3 R boundary ∧
        R ⊆ interior B ∧ frontier R = boundary ∧ frontier R ∩ M = band := by
  dsimp only
  obtain ⟨hhalf,hmeet,hboundary,H,hH,_,_⟩ :=
    exists_circle_surgery_boundary hβ τ hτ hfib hsphere caps hcaps hcapM hdis
  have hbandB : (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β) ⊆ interior B := by
    rintro _ ⟨z,hz,rfl⟩
    apply htubeB
    refine ⟨((z.1,0),z.2),⟨(signedTubeDiamond_coordinate_iff _).mpr ?_,hz.2⟩,rfl⟩
    rw [abs_zero,add_zero,abs_le]
    constructor <;> linarith [hz.1.1,hz.1.2]
  have hcv : Convex ℝ (TriangularRoofModel.halfBall 1) := by
    rw [TriangularRoofModel.halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage
      (TriangularRoofModel.halfBallForms 1 i)
  obtain ⟨R,hR,hRB,hRf⟩ := exists_confined_finitePL_sphere_ball hdim H hH
    (TriangularRoofModel.isCompact_halfBall (Or.inl rfl)) hcv
    (TriangularRoofModel.interior_halfBall_nonempty (Or.inl rfl)) (by simp)
    hB (union_subset hbandB (union_subset (hcapsB true) (hcapsB false)))
  exact ⟨hhalf,hmeet,R,hR,hRB,hRf,by rw [hRf]; exact hboundary⟩

end PoincareConjecture.M76

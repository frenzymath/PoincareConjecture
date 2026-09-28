import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.ReferenceMiddleInputs









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞



theorem saddle_reference_native_geometry_of_placement
    (u : UnitTwoSphere) (k d c rho rhoN Lambda deltaN : ℝ)
    (hrhoN : 0 < rhoN) (hLambda : 0 < Lambda)
    (hScale : Lambda * rhoN ^ 2 = rho ^ 2)
    (hsmallN : deltaN ≤ rhoN ^ 2 / 128)
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (kref : OpenPartialHomeomorph E2 E2)
    (gNative gRef : D2) (A : D3)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (Do Dc : Set UnitTwoSphere)
    (hgNative : EqOn gNative kref (closedBall (0 : E2) 2)) :
    let L := heightPlaneCoordinates u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let pi0 : E3 → E2 := fun y => (heightCoordinates y).1
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let j : UnitTwoSphere → E3 := fun p => nestedReferenceDiffeomorph d (p : E3)
    let Q : E2 → ℝ := fun x => (J2 x).1 ^ 2 - (J2 x).2 ^ 2
    (∀ y : E3, A y = L.symm
      (gRef (gNative.symm (pi0 y)), c + Lambda * (H0 y - k - d))) →
    (∀ x ∈ closedBall (0 : E2) 2,
      A (j (ks x)) = L.symm (gRef x, c + rho ^ 2 * Q x)) →
    (∀ t : ℝ, |t| < rho ^ 2 → ∀ p : UnitTwoSphere,
      H (A (j p)) = c + t →
      ((L (A (j p))).1 ∈ gRef '' ball (0 : E2) 1 ↔ p ∈ Do) ∧
      ((L (A (j p))).1 ∈ gRef '' closedBall (0 : E2) 1 ↔ p ∈ Dc)) →
    (∀ x ∈ closedBall (0 : E2) 2,
      pi0 (j (ks x)) = kref x ∧
      H0 (j (ks x)) = k + d + rhoN ^ 2 * Q x) ∧
    ∀ t : ℝ, |t| ≤ 2 * deltaN → ∀ p : UnitTwoSphere,
      H0 (j p) = k + d + t →
      (pi0 (j p) ∈ kref '' ball (0 : E2) 1 ↔ p ∈ Do) ∧
      (pi0 (j p) ∈ kref '' closedBall (0 : E2) 1 ↔ p ∈ Dc) := by
  intro L H pi0 H0 j Q hA hPlaced hPhysicalSheets
  have hLA (y : E3) : L (A y) =
      (gRef (gNative.symm (pi0 y)), c + Lambda * (H0 y - k - d)) := by
    rw [hA, L.apply_symm_apply]
  have hH (y : E3) : H (A y) = c + Lambda * (H0 y - k - d) := by
    change ⟪(u : E3), A y⟫_ℝ = c + Lambda * (H0 y - k - d)
    rw [← heightPlaneCoordinates_snd u]
    exact congrArg Prod.snd (hLA y)
  have hImage (S : Set E2) (hS : S ⊆ closedBall (0 : E2) 2) (v : E2) :
      gRef (gNative.symm v) ∈ gRef '' S ↔ v ∈ kref '' S := by
    constructor
    · rintro ⟨x, hx, heq⟩
      have hv : gNative x = v :=
        (congrArg gNative (gRef.injective heq)).trans (gNative.apply_symm_apply v)
      exact ⟨x, hx, (hgNative (hS hx)).symm.trans hv⟩
    · rintro ⟨x, hx, heq⟩
      refine ⟨x, hx, ?_⟩
      rw [← heq, ← hgNative (hS hx), gNative.symm_apply_apply]
  constructor
  · intro x hx
    have heq :
        (gRef (gNative.symm (pi0 (j (ks x)))), c + Lambda * (H0 (j (ks x)) - k - d)) =
          (gRef x, c + rho ^ 2 * Q x) := by
      rw [← hLA, hPlaced x hx, L.apply_symm_apply]
    have hplane : gNative.symm (pi0 (j (ks x))) = x :=
      gRef.injective (congrArg Prod.fst heq)
    have hheight : Lambda * (H0 (j (ks x)) - k - d) = rho ^ 2 * Q x :=
      add_left_cancel (congrArg Prod.snd heq)
    refine ⟨?_, ?_⟩
    · calc
        pi0 (j (ks x)) = gNative (gNative.symm (pi0 (j (ks x)))) :=
          (gNative.apply_symm_apply _).symm
        _ = gNative x := congrArg gNative hplane
        _ = kref x := hgNative hx
    · have hcancel : H0 (j (ks x)) - k - d = rhoN ^ 2 * Q x := by
        apply (mul_left_cancel₀ hLambda.ne')
        calc
          Lambda * (H0 (j (ks x)) - k - d) = rho ^ 2 * Q x := hheight
          _ = Lambda * (rhoN ^ 2 * Q x) := by rw [← hScale]; ring
      linarith only [hcancel]
  · intro t ht p hp
    have htime : |Lambda * t| < rho ^ 2 := by
      rw [abs_mul, abs_of_pos hLambda, ← hScale]
      apply mul_lt_mul_of_pos_left _ hLambda
      have hrhoN2 : 0 < rhoN ^ 2 := sq_pos_of_pos hrhoN
      linarith only [ht, hsmallN, hrhoN2]
    have hlevel : H (A (j p)) = c + Lambda * t := by
      rw [hH, hp]
      ring
    obtain ⟨hOpen, hClosed⟩ := hPhysicalSheets (Lambda * t) htime p hlevel
    rw [hLA] at hOpen hClosed
    have hBall : ball (0 : E2) 1 ⊆ closedBall (0 : E2) 2 :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
    have hClosedBall : closedBall (0 : E2) 1 ⊆ closedBall (0 : E2) 2 :=
      closedBall_subset_closedBall (by norm_num)
    exact ⟨(hImage _ hBall _).symm.trans hOpen,
      (hImage _ hClosedBall _).symm.trans hClosed⟩

end PoincareConjecture.M25.Topology3D

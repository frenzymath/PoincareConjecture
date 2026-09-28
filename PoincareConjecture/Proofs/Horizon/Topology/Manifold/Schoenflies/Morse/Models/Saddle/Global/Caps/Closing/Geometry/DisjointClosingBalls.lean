import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.ClosingBallBounds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.SeparatedClosures



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem exists_prepared_curved_closing_cap_point
    {v : E3} (hv : ‖v‖ = 1) (b w : Real) (hw : 0 < w)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y) :
    ∃ p ∈ Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v),
      inner Real v p = b + w ∧
      (Hemisphere.Plane v).orthogonalProjectionOnto (Q p) = A 0 := by
  let z := Reverse.capCoordinates hv A (0, b + w)
  have hz : z ∈ liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v :=
    (Reverse.mem_transported_cap_iff_flat hv b w hw.ne' A 0 (by simp) (b + w)).mpr rfl
  refine ⟨Q.symm z, mem_image_of_mem Q.symm hz, ?_, ?_⟩
  · rw [← hQ (Q.symm z), Q.apply_symm_apply]
    exact Reverse.inner_capCoordinates hv A (0, b + w)
  · rw [Q.apply_symm_apply]
    exact Reverse.projection_capCoordinates hv A (0, b + w)



theorem disjoint_closing_balls_of_disjoint_prepared_fillings
    {v : E3} (hv : ‖v‖ = 1) (b u w : Real) (hu : 0 < u) (hw : 0 < w)
    (A₁ A₂ : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (B₁ B₂ N₁ N₂ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN₁ : EqOn N₁ Q {y | b ≤ inner Real v y})
    (hN₂ : EqOn N₂ Q {y | b ≤ inner Real v y})
    (hΔ₁ : Q.symm '' (liftPlaneDiffeomorph hv b u hu.ne' A₁ '' boundedCylinderNorthernCap v) ⊆
      B₁ '' sphere (0 : E3) 1)
    (hΔ₂ : Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A₂ '' boundedCylinderNorthernCap v) ⊆
      B₂ '' sphere (0 : E3) 1)
    (hp₁ : ∀ y ∈ (B₁.trans N₁) '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A₁ '' closedBall 0 1)
    (hp₂ : ∀ y ∈ (B₂.trans N₂) '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A₂ '' closedBall 0 1)
    (hboundary : Disjoint (B₁ '' sphere (0 : E3) 1) (B₂ '' sphere (0 : E3) 1))
    (hplanar : Disjoint (A₁ '' closedBall (0 : Hemisphere.Plane v) 1) (A₂ '' closedBall 0 1)) :
    Disjoint (B₁ '' closedBall (0 : E3) 1) (B₂ '' closedBall (0 : E3) 1) := by
  obtain ⟨p, hp, hph, hpp⟩ := exists_prepared_curved_closing_cap_point hv b u hu A₁ Q hQ
  obtain ⟨q, hq, hqh, hqp⟩ := exists_prepared_curved_closing_cap_point hv b w hw A₂ Q hQ
  refine disjoint_closedBall_images_of_exterior_boundary_points B₁.toHomeomorph B₂.toHomeomorph
    hboundary (hΔ₁ hp) ?_ (hΔ₂ hq) ?_
  · intro hmem
    have hproj := prepared_closing_ball_projection_mem_filling A₂ B₂ N₂ Q hN₂ hp₂ hmem
      (by rw [hph]; linarith)
    rw [hpp] at hproj
    exact disjoint_left.mp hplanar (mem_image_of_mem A₁ (by simp)) hproj
  · intro hmem
    have hproj := prepared_closing_ball_projection_mem_filling A₁ B₁ N₁ Q hN₁ hp₁ hmem
      (by rw [hqh]; linarith)
    rw [hqp] at hproj
    exact disjoint_left.mp hplanar hproj (mem_image_of_mem A₂ (by simp))

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

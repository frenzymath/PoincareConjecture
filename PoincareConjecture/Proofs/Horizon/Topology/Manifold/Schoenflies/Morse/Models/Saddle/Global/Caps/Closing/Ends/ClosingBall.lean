import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.AxisReversal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem terminalCylinder_image_circle {v : E3}
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v)) (a b : Real) :
    terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
        (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
  rw [terminalCylinder_eq_height_product]
  ext y
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, ⟨q, hq, rfl⟩⟩, rfl⟩
    exact ⟨(t, q), ⟨ht, hq⟩, rfl⟩
  · rintro ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    exact ⟨(t, A q), ⟨ht, mem_image_of_mem A hq⟩, rfl⟩




theorem exists_curved_closing_ball_of_lower_cap_normalization
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b s w : Real} (hab : a ≤ b) (hs : s < 0) (hw : 0 < w)
    (N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    {E : Set E3}
    (himage : N '' E =
      liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b) :
    ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B '' sphere (0 : E3) 1 = E ∪
        Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) := by
  let U := liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v
  have hUheight : U ⊆ {y | b ≤ inner Real v y} := by
    rintro y ⟨x, hx, rfl⟩
    change b ≤ inner Real v (liftPlaneDiffeomorph hv b w hw.ne' A x)
    rw [inner_liftPlaneDiffeomorph]
    exact le_add_of_nonneg_right
      (mul_nonneg hw.le (height_nonneg_of_mem_boundedCylinderNorthernCap hx))
  have hQinv (y : E3) : inner Real v (Q.symm y) = inner Real v y := by
    rw [← hQ (Q.symm y), Q.apply_symm_apply]
  have hinv : EqOn N.symm Q.symm U := by
    intro y hy
    apply N.injective
    change N (N.symm y) = N (Q.symm y)
    rw [N.apply_symm_apply, hN (by
      change b ≤ inner Real v (Q.symm y)
      rw [hQinv]
      exact hUheight hy), Q.apply_symm_apply]
  obtain ⟨F, hF⟩ := exists_ambient_capped_cylinder_of_scales hv a b hab
    (-s) w (neg_pos.mpr hs) hw A
  have hboundary : F '' sphere (0 : E3) 1 = N '' E ∪ U := by
    rw [himage, terminalCylinder_image_circle]
    simpa only [neg_neg, boundedCylinderNorthernCap, U] using hF
  refine ⟨F.trans N.symm, ?_⟩
  change (N.symm ∘ F) '' sphere (0 : E3) 1 = _
  rw [image_comp, hboundary, image_union, image_image]
  simp only [N.symm_apply_apply, image_id']
  rw [image_congr hinv]




theorem exists_common_curved_closing_balls_of_lower_cap_normalizations
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {a d b s t w : Real} (hab : a < b) (hdb : d < b)
    (hs : s < 0) (ht : t < 0) (hw : 0 < w)
    (N₁ N₂ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN₁ : EqOn N₁ Q {y | b ≤ inner Real v y})
    (hN₂ : EqOn N₂ Q {y | b ≤ inner Real v y})
    {E M : Set E3}
    (hE : N₁ '' E = liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
      terminalCylinder (range γ) a b)
    (hM : N₂ '' M = liftPlaneDiffeomorph hv d t ht.ne B '' boundedCylinderNorthernCap v ∪
      terminalCylinder (range γ) d b) :
    ∃ B₁ B₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B₁ '' sphere (0 : E3) 1 = E ∪
        Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) ∧
      B₂ '' sphere (0 : E3) 1 = M ∪
        Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) := by
  obtain ⟨D, hDhalf, hDcircle, hDcap⟩ :=
    exists_complete_lower_cap_alignment hv γ hγ A B hA hB hdb ht
  have hDcylinder : D '' terminalCylinder (range γ) d b =
      terminalCylinder (range γ) d b := by
    have hfix : EqOn D id (terminalCylinder (range γ) d b) := by
      rintro y ⟨⟨x, z⟩, ⟨⟨q, rfl⟩, hz⟩, rfl⟩
      exact hDcircle z q
    rw [image_congr hfix, image_id]
  have hN₂' : EqOn (N₂.trans D) Q {y | b ≤ inner Real v y} := by
    intro y hy
    change D (N₂ y) = Q y
    rw [hN₂ hy]
    exact hDhalf _ (by rw [hQ]; exact hy)
  have hM' : (N₂.trans D) '' M =
      liftPlaneDiffeomorph hv d t ht.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) d b := by
    change (D ∘ N₂) '' M = _
    rw [image_comp, hM, image_union, hDcap, hDcylinder, hA]
  obtain ⟨B₁, hB₁⟩ := exists_curved_closing_ball_of_lower_cap_normalization hv A hab.le hs hw
    N₁ Q hQ hN₁ (by simpa only [hA] using hE)
  obtain ⟨B₂, hB₂⟩ := exists_curved_closing_ball_of_lower_cap_normalization hv A hdb.le ht hw
    (N₂.trans D) Q hQ hN₂' hM'
  exact ⟨B₁, B₂, hB₁, hB₂⟩



theorem image_closing_ball_of_cap_image
    (F B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {E M Δ : Set E3}
    (hB : B '' sphere (0 : E3) 1 = E ∪ Δ)
    (hL : L '' sphere (0 : E3) 1 = M ∪ Δ)
    (hcap : F '' E = M) (hclose : EqOn F id Δ) :
    F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
      F '' (B '' ball (0 : E3) 1) = L '' ball (0 : E3) 1 := by
  have hboundary : (B.trans F) '' sphere (0 : E3) 1 = L '' sphere (0 : E3) 1 := by
    change (F ∘ B) '' sphere (0 : E3) 1 = _
    rw [image_comp, hB, image_union, hcap, image_congr hclose, image_id, hL]
  have hdim : 1 < Module.rank Real E3 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hclosed := (B.trans F).toHomeomorph.image_closedBall_eq_of_image_sphere_eq
    L.toHomeomorph hdim hboundary
  have hopen := (B.trans F).toHomeomorph.image_ball_eq_of_image_sphere_eq
    L.toHomeomorph hdim hboundary
  change (F ∘ B) '' closedBall (0 : E3) 1 = L '' closedBall (0 : E3) 1 at hclosed
  change (F ∘ B) '' ball (0 : E3) 1 = L '' ball (0 : E3) 1 at hopen
  rw [image_comp] at hclosed hopen
  exact ⟨hclosed, hopen⟩




theorem transported_inner_closing_ball_subset
    (F B L J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {E M Δ : Set E3}
    (hB : B '' sphere (0 : E3) 1 = E ∪ Δ)
    (hL : L '' sphere (0 : E3) 1 = M ∪ Δ)
    (hcap : F '' E = M) (hclose : EqOn F id Δ)
    (hinner : J '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1) :
    (J.trans F) '' closedBall (0 : E3) 1 ⊆ L '' ball (0 : E3) 1 := by
  have hball := (image_closing_ball_of_cap_image F B L hB hL hcap hclose).2
  change (F ∘ J) '' closedBall (0 : E3) 1 ⊆ _
  rw [image_comp, ← hball]
  exact image_mono hinner

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

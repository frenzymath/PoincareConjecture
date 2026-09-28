import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.ClosingBallBounds
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ClosingBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem normalized_curved_closing_boundary_projection
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b s w : Real} (hs : s < 0) (hw : 0 < w)
    (B N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    {E : Set E3}
    (hE : N '' E =
      liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b)
    (hB : B '' sphere (0 : E3) 1 = E ∪
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)) :
    ∀ y ∈ (B.trans N) '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 := by
  intro y hy
  change y ∈ (N ∘ B) '' sphere (0 : E3) 1 at hy
  rw [image_comp, hB, image_union, hE] at hy
  rcases hy with (hy | hy) | ⟨z, ⟨u, hu, rfl⟩, rfl⟩
  · exact (Reverse.transported_cap_bounds hv a s hs.ne A hy).2.1
  · rw [terminalCylinder_eq_height_product] at hy
    obtain ⟨⟨t, x⟩, ⟨_, hx⟩, rfl⟩ := hy
    simpa [Hemisphere.Plane,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
      using image_mono sphere_subset_closedBall hx
  · have hheight : b ≤ inner Real v (Q.symm u) := by
      have hhu := (Reverse.transported_cap_bounds hv b w hw.ne' A hu).1
      have hinv : inner Real v (Q.symm u) = inner Real v u := by
        rw [← hQ (Q.symm u), Q.apply_symm_apply]
      rw [hinv]
      have hh := mul_nonneg hhu hw.le
      rw [div_mul_cancel₀ _ hw.ne'] at hh
      linarith
    rw [hN hheight, Q.apply_symm_apply]
    exact (Reverse.transported_cap_bounds hv b w hw.ne' A hu).2.1



theorem normalized_cap_terminal_slice_subset_closing_disk
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b s w : Real} (hab : a < b) (hs : s < 0) (hw : 0 < w)
    (N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    {E : Set E3}
    (hE : N '' E =
      liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b)
    {y : E3} (hy : y ∈ E) (hheight : inner Real v y = b) :
    y ∈ Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) := by
  have hNy : N y = Q y := hN hheight.ge
  have hh : inner Real v (N y) = b := by rw [hNy, hQ, hheight]
  have hc : N y ∈ terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b := by
    have hm := mem_image_of_mem N hy
    rw [hE] at hm
    rcases hm with ⟨z, hz, heq⟩ | hm
    · have hzheight := height_nonneg_of_mem_boundedCylinderNorthernCap hz
      have hle : inner Real v (N y) ≤ a := by
        rw [← heq, inner_liftPlaneDiffeomorph]
        nlinarith
      exact (hab.not_ge (hh ▸ hle)).elim
    · exact hm
  rw [terminalCylinder_eq_height_product] at hc
  obtain ⟨⟨t, x⟩, ⟨_, ⟨q, hq, rfl⟩⟩, heq⟩ := hc
  have ht : t = b := by
    rw [← heq] at hh
    change inner Real v (heightCoordinates hv (t, A q)) = b at hh
    rw [inner_heightCoordinates] at hh
    exact hh
  subst t
  have hrim : N y ∈ (fun x : Hemisphere.Plane v => b • v + (A x : E3)) '' sphere 0 1 :=
    ⟨q, hq, heq⟩
  have hslice := lifted_cap_slice_eq_circle hv b w hw.ne' A
    (show (0 : Real) ∈ Ico 0 1 by constructor <;> norm_num)
  simp only [mul_zero, add_zero] at hslice
  rw [← hslice] at hrim
  exact ⟨N y, hrim.1, by rw [hNy, Q.symm_apply_apply]⟩



theorem normalized_curved_closing_ball_inter_band
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b s w : Real} (hab : a < b) (hs : s < 0) (hw : 0 < w)
    (B N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    {E band : Set E3} (hEheight : ∀ y ∈ E, inner Real v y ≤ b)
    (hE : N '' E =
      liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b)
    (hB : B '' sphere (0 : E3) 1 = E ∪
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v))
    (hband : ∀ y ∈ band, b ≤ inner Real v y)
    (havoid : ∀ y ∈ band, inner Real v y ≤ b + 2 * w →
      (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∉ A '' ball 0 1) :
    (B '' closedBall (0 : E3) 1) ∩ band ⊆
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) := by
  apply closing_ball_inter_band_subset_closing_disk A B N Q hB hN
    (normalized_curved_closing_boundary_projection hv A hs hw B N Q hQ hN hE hB)
    (curved_closing_ball_height_le hv b w hw A B Q hQ hEheight hB) hband havoid
  rintro y ⟨hy, hyband⟩
  exact normalized_cap_terminal_slice_subset_closing_disk hv A hab hs hw N Q hQ hN hE hy
    (le_antisymm (hEheight y hy) (hband y hyband))

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.BandEndpoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapCollar



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem image_upper_cap_of_constant_plane_action
    {v : E3} (hv : ‖v‖ = 1) {b c s : Real} (hbc : b ≤ c) (hs : 0 < s)
    (A Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ (t : Real) (x : Hemisphere.Plane v), b ≤ t →
      D (t • v + (x : E3)) = t • v + (Q x : E3)) :
    D '' (liftPlaneDiffeomorph hv c s hs.ne' A '' boundedCylinderNorthernCap v) =
      liftPlaneDiffeomorph hv c s hs.ne' (A.trans Q) '' boundedCylinderNorthernCap v := by
  rw [← image_comp]
  apply image_congr
  intro y hy
  change D (liftPlaneDiffeomorph hv c s hs.ne' A y) =
    liftPlaneDiffeomorph hv c s hs.ne' (A.trans Q) y
  rw [liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply,
    hD _ _ (hbc.trans (le_add_of_nonneg_right
      (mul_nonneg hs.le (height_nonneg_of_mem_boundedCylinderNorthernCap hy))))]
  rfl


theorem image_lower_cap_of_fixed_lower_halfSpace
    {v : E3} (hv : ‖v‖ = 1) {a c s : Real} (hca : c ≤ a) (hs : 0 < s)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ x, inner Real v x ≤ a → D x = x) :
    D '' (liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs.ne') A ''
      boundedCylinderNorthernCap v) =
      liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs.ne') A ''
        boundedCylinderNorthernCap v := by
  calc
    _ = id '' (liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs.ne') A ''
        boundedCylinderNorthernCap v) := by
      apply image_congr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      apply hD
      rw [inner_liftPlaneDiffeomorph]
      have hnonneg := height_nonneg_of_mem_boundedCylinderNorthernCap hz
      nlinarith
    _ = _ := image_id _

end Poincare.Manifold.Schoenflies

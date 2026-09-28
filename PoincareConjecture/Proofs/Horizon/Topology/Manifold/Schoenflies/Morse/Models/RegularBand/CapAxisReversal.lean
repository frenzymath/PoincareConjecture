import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.AxisReversal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapCollar

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem neg_mem_boundedCylinderNorthernCap {v y : E3}
    (hy : y ∈ boundedCylinderNorthernCap v) : -y ∈ boundedCylinderNorthernCap (-v) := by
  obtain ⟨p, hp, rfl⟩ := hy
  let q : S2 := ⟨-(p : E3), by simpa only [mem_sphere, dist_zero_right, norm_neg]
    using p.property⟩
  refine ⟨q, ?_, ?_⟩
  · change 0 ≤ inner Real (-v) (-(p : E3))
    simpa only [inner_neg_neg] using (show 0 ≤ inner Real v (p : E3) from hp)
  · simp only [q, boundedCylinderRadius, inner_neg_neg, smul_neg]

theorem image_neg_boundedCylinderNorthernCap (v : E3) :
    Neg.neg '' boundedCylinderNorthernCap v = boundedCylinderNorthernCap (-v) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact neg_mem_boundedCylinderNorthernCap hx
  · intro y hy
    refine ⟨-y, ?_, neg_neg y⟩
    simpa only [neg_neg] using neg_mem_boundedCylinderNorthernCap hy

theorem image_liftPlaneDiffeomorph_axis_neg {v : E3} (hv : ‖v‖ = 1)
    (c s : Real) (hs : s ≠ 0) (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v)) :
    liftPlaneDiffeomorph (by simpa using hv : ‖-v‖ = 1)
        (-c) (-s) (neg_ne_zero.mpr hs) (axisNegPlaneDiffeomorph v A) ''
          boundedCylinderNorthernCap (-v) =
      liftPlaneDiffeomorph hv c s hs A '' boundedCylinderNorthernCap v := by
  rw [← image_neg_boundedCylinderNorthernCap, image_image]
  exact image_congr (fun x _ => liftPlaneDiffeomorph_axis_neg v hv c s hs A x)

end Poincare.Manifold.Schoenflies

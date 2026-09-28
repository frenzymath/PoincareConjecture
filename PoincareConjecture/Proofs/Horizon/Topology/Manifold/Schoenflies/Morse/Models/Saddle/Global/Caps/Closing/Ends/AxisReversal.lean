import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CanonicalAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapAxisReversal

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem terminalCylinder_eq_height_product {v : E3}
    (Q : Set (Hemisphere.Plane v)) (a b : Real) :
    terminalCylinder Q a b =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) '' (Icc a b ×ˢ Q) := by
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩

theorem terminalCylinder_axis_neg {v : E3}
    (Q : Set (Hemisphere.Plane v)) (a b : Real) :
    terminalCylinder (axisNegPlaneEquiv v '' Q) (-b) (-a) = terminalCylinder Q a b := by
  ext y
  constructor
  · rintro ⟨⟨_, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
    refine ⟨(x, -t), ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
    simp only [coe_axisNegPlaneEquiv, neg_smul, smul_neg]
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    refine ⟨(axisNegPlaneEquiv v x, -t),
      ⟨mem_image_of_mem _ hx, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
    simp only [coe_axisNegPlaneEquiv, neg_smul, smul_neg, neg_neg]

theorem complete_canonical_cap_axis_neg {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (Q : Set (Hemisphere.Plane v)) (a b s : Real) (hs : s ≠ 0) :
    (liftPlaneDiffeomorph (by simpa using hv : ‖-v‖ = 1)
      (-b) (-s) (neg_ne_zero.mpr hs) (axisNegPlaneDiffeomorph v A) ''
        boundedCylinderNorthernCap (-v)) ∪
      terminalCylinder (axisNegPlaneEquiv v '' Q) (-b) (-a) =
    (liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) ∪
      terminalCylinder Q a b := by
  rw [image_liftPlaneDiffeomorph_axis_neg, terminalCylinder_axis_neg]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

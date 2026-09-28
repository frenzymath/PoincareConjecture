import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapGeometry







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
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



theorem curved_closing_cap_height_of_interior_projection
    {v : E3} (hv : ‖v‖ = 1) (b w : Real) (hw : 0 < w)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {y : E3}
    (hy : y ∈ liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)
    (hp : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) :
    b + w ≤ inner Real v y := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [projection_liftPlaneDiffeomorph] at hp
  obtain ⟨q, hq, heq⟩ := hp
  have hn : ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖ < 1 := by
    rw [← A.injective heq]
    exact mem_ball_zero_iff.mp hq
  have hh := (mem_boundedCylinderNorthernCap_iff_height hv hn).mp hz
  have hsq : ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto z)]
  have hge := one_le_boundedCapHeight
    (sq_nonneg ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖) hsq
  rw [inner_liftPlaneDiffeomorph, hh]
  nlinarith



theorem disjoint_curved_closing_caps_of_disjoint_fillings
    {v : E3} (hv : ‖v‖ = 1) (b u w : Real) (hu : 0 < u) (hw : 0 < w)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hAB : Disjoint (A '' closedBall 0 1) (B '' closedBall 0 1)) :
    Disjoint
      (liftPlaneDiffeomorph hv b u hu.ne' A '' boundedCylinderNorthernCap v)
      (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) := by
  apply disjoint_left.mpr
  intro y hyA hyB
  exact disjoint_left.mp hAB
    (Reverse.transported_cap_bounds hv b u hu.ne' A hyA).2.1
    (Reverse.transported_cap_bounds hv b w hw.ne' B hyB).2.1




theorem disjoint_curved_closing_caps_of_nested_fillings
    {v : E3} (hv : ‖v‖ = 1) (b u w : Real) (hu : 0 < u) (hw : 0 < w)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hAB : A '' closedBall 0 1 ⊆ B '' ball 0 1) (hscale : 2 * u < w) :
    Disjoint
      (liftPlaneDiffeomorph hv b u hu.ne' A '' boundedCylinderNorthernCap v)
      (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) := by
  apply disjoint_left.mpr
  intro y hyA hyB
  have hA := Reverse.transported_cap_bounds hv b u hu.ne' A hyA
  have hB := curved_closing_cap_height_of_interior_projection hv b w hw B hyB
    (hAB hA.2.1)
  have hupper := (abs_le.mp hA.2.2).2
  rw [abs_of_pos hu] at hupper
  linarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

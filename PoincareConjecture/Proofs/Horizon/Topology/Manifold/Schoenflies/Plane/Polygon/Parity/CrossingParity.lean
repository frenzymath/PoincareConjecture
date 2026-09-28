import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.CrossingBasics
import Mathlib.Geometry.Polygon.Basic











set_option autoImplicit false

open scoped BigOperators

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}



noncomputable def polygonCrossingParity (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ) (q : E) : ZMod 2 :=
  ∑ i, segmentRayParity X H (p i) (p (finRotate n i)) q



theorem sum_heightStep_cyclic (p : Polygon E n) (H : E →ₗ[ℝ] ℝ) (y : ℝ) :
    ∑ i, (heightStep (H (p i)) y + heightStep (H (p (finRotate n i))) y) = 0 := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp (finRotate n) (fun i => heightStep (H (p i)) y)]
  exact CharTwo.add_self_eq_zero _



theorem polygonCrossingParity_eq_zero_of_right (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ) (q : E)
    (hq : ∀ i, X (p i) ≤ X q) : polygonCrossingParity p X H q = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact segmentRayParity_eq_zero_of_right_endpoints X H (hq i) (hq (finRotate n i))



theorem polygonCrossingParity_eq_zero_of_left (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ) (q : E)
    (hq : ∀ i, X q < X (p i)) : polygonCrossingParity p X H q = 0 := by
  calc
    polygonCrossingParity p X H q =
        ∑ i, (heightStep (H (p i)) (H q) + heightStep (H (p (finRotate n i))) (H q)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact segmentRayParity_eq_heightStep_of_left_endpoints X H
        (hq i) (hq (finRotate n i))
    _ = 0 := sum_heightStep_cyclic p H (H q)

end Poincare.Manifold.Schoenflies.Plane

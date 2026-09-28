import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import PoincareConjecture.Proofs.M49.Mathlib.TensorContraction

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M49

theorem roundCylinderTensorNormSquared_nonneg (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (hG : ((roundCylinderGram u c p)⁻¹).PosSemidef)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u c p T := by
  simpa only [roundCylinderTensorNormSquared] using!
    Matrix.tensor_contraction_nonneg hG T

theorem roundCylinder_zeroth_le_jetErrorSquared (u : ℝ)
    (B : RoundCylinderTwoTensor) (k : ℕ) (z : RoundCylinderSpace)
    (hG : ((roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2))⁻¹).PosSemidef) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          B 0 ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)) ≤
      roundCylinderJetErrorSquared u B k z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.single_le_sum
    (f := fun j => roundCylinderTensorNormSquared u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)
      (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B j ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)))
    (fun j _ => roundCylinderTensorNormSquared_nonneg _ _ _ hG _)
    (Finset.mem_range.mpr (Nat.zero_lt_succ k))

end PoincareConjecture.M49

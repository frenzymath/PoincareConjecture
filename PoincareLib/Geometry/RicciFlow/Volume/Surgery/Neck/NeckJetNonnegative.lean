import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Analysis.TensorContraction

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/NeckJetNonnegative.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Extracting the actual zeroth round-cylinder jet term

Morgan-Tian Definition 2.16, p. 30, and Definition 2.18, p. 31,
use the inverse-Gram contraction on every covariant slot. The explicit
matrix positivity hypothesis below will be supplied by the literal
scalar-curvature-one cylinder geometry.
-/

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareMT.SurgeryVolume

/-- Each raw cylinder contraction is nonnegative when its actual inverse
Gram matrix is positive semidefinite (MT Definition 2.16, p. 30). -/
theorem roundCylinderTensorNormSquared_nonneg (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (hG : ((roundCylinderGram u c p)⁻¹).PosSemidef)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u c p T := by
  simpa only [roundCylinderTensorNormSquared] using!
    Matrix.tensor_contraction_nonneg hG T

/-- The actual zeroth metric-error term is bounded by the full jet sum
under its inverse-Gram sign condition (MT Definition 2.16, p. 30). -/
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

end PoincareMT.SurgeryVolume

import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.BilinearJetBounds
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.QuantitativeJets
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization

/-!
# Numerical derivatives of the centered cylinder metric

The centered stereographic coefficients have zero first derivative. Their
second scalar jets have norm at most eighteen, and summing the nine metric
components gives the bilinear second-derivative bound of 162.

Reference: Morgan--Tian, Lemma A.2, pp. 497-498; Proposition A.11, pp. 503-504.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

namespace PoincareMT

/-- The model coefficient field has zero first derivative at the center. -/
theorem fderiv_roundCylinderEuclideanCoefficients_zero :
    fderiv ℝ roundCylinderEuclideanCoefficients 0 = 0 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components
    contDiff_roundCylinderEuclideanCoefficients.contDiffAt 1 (C := 0)
    (fun i j => by
      rw [norm_iteratedFDeriv_one,
        roundCylinderEuclideanCoefficients_scalar_fderiv_zero q i j, norm_zero])
  simpa only [norm_iteratedFDeriv_one, mul_zero, norm_le_zero_iff] using h

/-- A numerical operator bound for the full second derivative of the model. -/
theorem norm_second_fderiv_roundCylinderEuclideanCoefficients_zero_le :
    ‖fderiv ℝ (fderiv ℝ roundCylinderEuclideanCoefficients) 0‖ ≤ 162 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components
    contDiff_roundCylinderEuclideanCoefficients.contDiffAt 2 (C := 18)
    (roundCylinderEuclideanCoefficients_scalar_second_le q)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h
  norm_num at h ⊢
  exact h

end PoincareMT

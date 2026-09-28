import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.BilinearJetBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.QuantitativeJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

namespace PoincareConjecture

theorem fderiv_roundCylinderEuclideanCoefficients_zero :
    fderiv ℝ roundCylinderEuclideanCoefficients 0 = 0 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components
    contDiff_roundCylinderEuclideanCoefficients.contDiffAt 1 (C := 0)
    (fun i j => by
      rw [norm_iteratedFDeriv_one,
        roundCylinderEuclideanCoefficients_scalar_fderiv_zero q i j, norm_zero])
  simpa only [norm_iteratedFDeriv_one, mul_zero, norm_le_zero_iff] using h

theorem norm_second_fderiv_roundCylinderEuclideanCoefficients_zero_le :
    ‖fderiv ℝ (fderiv ℝ roundCylinderEuclideanCoefficients) 0‖ ≤ 162 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components
    contDiff_roundCylinderEuclideanCoefficients.contDiffAt 2 (C := 18)
    (roundCylinderEuclideanCoefficients_scalar_second_le q)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h
  norm_num at h ⊢
  exact h

end PoincareConjecture

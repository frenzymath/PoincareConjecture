import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ModelConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.InverseGram
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.EuclideanModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

theorem roundCylinderEuclideanMetric_gram_zero :
    (Matrix.of (fun i j => roundCylinderEuclideanMetric.inner 0
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j))) =
        NeckCurvature.cylinderGramDiagonal := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  ext i j
  simp only [Matrix.of_apply, roundCylinderEuclideanMetric_inner]
  rw [roundCylinderEuclideanCoefficients_basis q 0]
  simp only [map_zero, add_zero]
  rw [roundCylinderGram_eq_stereographic_formula]
  fin_cases i <;> fin_cases j <;>
    norm_num [NeckCurvature.cylinderGramDiagonal, Matrix.diagonal_apply,
      roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.ext_iff]

private theorem model_scalar_jet_eq_cylinder (q : UnitTwoSphere)
    (r : ℕ) (i j : Fin 3) (a : Fin r → Fin 3) :
    iteratedFDeriv ℝ r (fun x => roundCylinderEuclideanMetric.inner x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0
        (fun k => roundCylinderEuclideanBasis (a k)) =
      iteratedFDeriv ℝ r (fun p => roundCylinderGram 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) (0, 0)
        (fun k => roundCylinderCoordinateBasis (a k)) := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have heq : (fun x => roundCylinderEuclideanMetric.inner x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) =
      (fun p => roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) ∘ T := by
    funext x
    rw [roundCylinderEuclideanMetric_inner, roundCylinderEuclideanCoefficients_basis q 0]
    simp only [Function.comp_apply, Prod.mk_zero_zero, zero_add]
    rfl
  rw [heq, Poincare.Analysis.Calculus.iteratedFDeriv_comp_continuousLinearEquiv]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
    ContinuousLinearEquiv.coe_coe, T, lineModelEquiv_symm_roundCylinderEuclideanBasis]
  rfl

theorem roundCylinderEuclideanMetric_first_scalar_jet_zero (i j k : Fin 3) :
    fderiv ℝ (fun x => roundCylinderEuclideanMetric.inner x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0
        (roundCylinderEuclideanBasis k) = 0 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := model_scalar_jet_eq_cylinder q 1 i j ![k]
  simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero,
    fderiv_roundCylinderGram_center, zero_apply] using h

theorem roundCylinderEuclideanMetric_second_scalar_jet
    (i j k l : Fin 3) :
    fderiv ℝ (fderiv ℝ (fun x => roundCylinderEuclideanMetric.inner x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j))) 0
        (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l) =
      -2 * inner ℝ (roundCylinderCoordinateBasis k).1 (roundCylinderCoordinateBasis l).1 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  have h := model_scalar_jet_eq_cylinder q 2 i j ![k, l]
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, fderiv_fderiv_roundCylinderGram_center] using h

end PoincareConjecture

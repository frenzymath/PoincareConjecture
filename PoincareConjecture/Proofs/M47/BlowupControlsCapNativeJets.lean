import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeDerivative
import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cap_native_iterated_metricDifference
    (u : ℝ) (hu : u < 1) (g1 : RiemannianMetric 3 E₃)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) {U : Set E₃} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E₂ q) (M35.cylinderCoordinateEquiv x) i j)
    (k : ℕ) {x : E₃} (hx : x ∈ U) (a : Fin (2 + k) → Fin 3) :
    D0.iteratedCovariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) -
          (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)) k x
      (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) =
      roundCylinderIteratedDerivative u (chartAt E₂ q) B k (M35.cylinderCoordinateEquiv x) a := by
  let H : CovariantTensorEvaluation 3 E₃ 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
  change D0.iteratedCovariantTensorDerivative H k x
    (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) = _
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth _ _
  induction k generalizing x with
  | zero =>
    change g1.inner x _ _ - (M35.cylinderEuclideanMetric u hu).inner x _ _ = _
    rw [hcoeff x hx, M35.cylinderEuclideanMetric_basis u hu q]
    rfl
  | succ k ih =>
    let T := D0.iteratedCovariantTensorDerivative H k
    have hT : IsSmoothCovariantTensor T := cap_iteratedCovariantTensorDerivative_smooth D0 H hH k
    change D0.covariantTensorDerivative T x _ = _
    refine (cap_model_covariantTensorDerivative_native u hu D0 q T hT x a).trans ?_
    have heq (b : Fin (2 + k) → Fin 3) :
        (fun p : RoundCylinderCoordinates => T (M35.cylinderCoordinateEquiv.symm p)
          (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (b j))) =ᶠ[𝓝 (M35.cylinderCoordinateEquiv x)]
        (fun p => roundCylinderIteratedDerivative u (chartAt E₂ q) B k p b) := by
      have hV : IsOpen (M35.cylinderCoordinateEquiv.symm ⁻¹' U) :=
        hU.preimage M35.cylinderCoordinateEquiv.symm.continuous
      have hxV : M35.cylinderCoordinateEquiv x ∈ M35.cylinderCoordinateEquiv.symm ⁻¹' U := by
        simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
      filter_upwards [hV.mem_nhds hxV] with p hp
      have h := ih hp b
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using h
    change roundCylinderTensorDerivative u (chartAt E₂ q) _ (M35.cylinderCoordinateEquiv x) a =
      roundCylinderTensorDerivative u (chartAt E₂ q)
        (roundCylinderIteratedDerivative u (chartAt E₂ q) B k) (M35.cylinderCoordinateEquiv x) a
    unfold roundCylinderTensorDerivative
    congr 1
    · exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
        L (roundCylinderCoordinateBasis (a 0))) (heq (fun j => a j.succ)).fderiv_eq
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact (heq (Function.update (fun l => a l.succ) i j)).self_of_nhds

theorem cap_native_metricDifference_norm_sq
    (g1 : RiemannianMetric 3 E₃)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num)))
    (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) {U : Set E₃} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E₂ q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) (k : ℕ) :
    let H : CovariantTensorEvaluation 3 E₃ 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
    ((M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 =
      roundCylinderTensorNormSquared 0 (chartAt E₂ q) (chartAt E₂ q q, s)
        (roundCylinderIteratedDerivative 0 (chartAt E₂ q) B k (chartAt E₂ q q, s)) := by
  dsimp only
  let H : CovariantTensorEvaluation 3 E₃ 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth _ _
  have hT := cap_iteratedCovariantTensorDerivative_smooth D0 H hH k
  rw [cap_native_tensorNorm_sq q s _ (hT.1 _)]
  congr 1
  funext a
  have h := cap_native_iterated_metricDifference 0 (by norm_num) g1 D0 q B hU hcoeff k hx a
  simpa only [ContinuousLinearEquiv.apply_symm_apply, M35.sphere_chart_center] using h

end PoincareConjecture.M47

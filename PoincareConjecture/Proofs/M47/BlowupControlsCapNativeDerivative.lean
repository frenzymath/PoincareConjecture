import PoincareConjecture.Proofs.M47.BlowupControlsCapMetricError
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLeviCivita
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private theorem native_constant_field_smooth (v : E₃) :
    ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun x : E₃ => Bundle.TotalSpace.mk' E₃ x (E := TangentSpace (𝓡 3)) v) univ := by
  intro x _
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩

private theorem native_tensor_update_sum {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r) (hT : IsSmoothCovariantTensor T)
    (x : E₃) (a : Fin r → Fin 3) (i : Fin r) (v : E₃) :
    T x (Function.update (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) i v) =
      ∑ k, v k * T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ
        (Function.update a i k j)) := by
  classical
  obtain ⟨A, hA⟩ := hT.1 x
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hrec : (∑ k, v k • b k) = v := by
    simpa only [b, EuclideanSpace.basisFun_repr] using b.sum_repr v
  rw [hA]
  conv_lhs => rw [← hrec]
  rw [A.map_update_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [A.map_update_smul]
  simp only [smul_eq_mul]
  congr 1
  rw [hA]
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, b]




theorem cap_covariantTensorDerivative_coordinates
    {g : RiemannianMetric 3 E₃} (D : LeviCivitaData g) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r) (hT : IsSmoothCovariantTensor T)
    (x : E₃) (a : Fin (r + 1) → Fin 3) :
    D.covariantTensorDerivative T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) =
      fderiv ℝ (fun y => T y (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j.succ)))
        x (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) -
      ∑ i : Fin r, ∑ k : Fin 3,
        (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ (a 0))
          (EuclideanSpace.basisFun (Fin 3) ℝ (a i.succ)) x) k *
        T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ
          (Function.update (fun l => a l.succ) i k j)) := by
  let X : Fin (r + 1) → (y : E₃) → TangentSpace (𝓡 3) y :=
    fun j _ => EuclideanSpace.basisFun (Fin 3) ℝ (a j)
  have hX : ∀ j, ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% (X j)) univ :=
    fun j => native_constant_field_smooth _
  have h := M04.covariantTensorDerivativeOnFields_eq D hT isOpen_univ hX (mem_univ x)
  rw [← h]
  unfold M04.covariantTensorDerivativeOnFields
  simp only [X, mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact native_tensor_update_sum T hT x (fun j => a j.succ) i _



theorem cap_model_covariantTensorDerivative_coordinates
    (u : ℝ) (hu : u < 1) (D : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r) (hT : IsSmoothCovariantTensor T)
    (x : E₃) (a : Fin (r + 1) → Fin 3) :
    D.covariantTensorDerivative T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) =
      fderiv ℝ (fun y => T y (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j.succ)))
        x (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) -
      ∑ i : Fin r, ∑ k : Fin 3,
        roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (M35.cylinderCoordinateEquiv x) k (a 0) (a i.succ) *
        T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ
          (Function.update (fun l => a l.succ) i k j)) := by
  rw [cap_covariantTensorDerivative_coordinates D T hT]
  simp only [M35.cylinder_connection_component u hu D q]




theorem cap_model_covariantTensorDerivative_native
    (u : ℝ) (hu : u < 1) (D : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r) (hT : IsSmoothCovariantTensor T)
    (x : E₃) (a : Fin (r + 1) → Fin 3) :
    D.covariantTensorDerivative T x (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) =
      roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (fun p b => T (M35.cylinderCoordinateEquiv.symm p)
          (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (b j)))
        (M35.cylinderCoordinateEquiv x) a := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let f : E₃ → ℝ := fun y => T y (fun j => b (a j.succ))
  have hf : DifferentiableAt ℝ f x := by
    have hs := hT.2 univ isOpen_univ (fun j _ => b (a j.succ))
      (fun j => native_constant_field_smooth _)
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((hs.contMDiffAt (by simp)).mdifferentiableAt (by simp))
  have hfc : DifferentiableAt ℝ f
      (M35.cylinderCoordinateEquiv.symm (M35.cylinderCoordinateEquiv x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  have hc := hfc.hasFDerivAt.comp (M35.cylinderCoordinateEquiv x)
    M35.cylinderCoordinateEquiv.symm.hasFDerivAt
  have hd := congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
    L (M35.cylinderCoordinateEquiv (b (a 0)))) hc.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at hd
  have hder :
      fderiv ℝ (fun p => f (M35.cylinderCoordinateEquiv.symm p))
        (M35.cylinderCoordinateEquiv x) (roundCylinderCoordinateBasis (a 0)) =
      fderiv ℝ f x (b (a 0)) := by
    simpa only [b, Function.comp_def, M35.cylinderCoordinateEquiv_basis] using hd
  rw [cap_model_covariantTensorDerivative_coordinates u hu D q T hT]
  unfold roundCylinderTensorDerivative
  dsimp only
  rw [hder]
  simp only [f, b]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (congrArg (fun y : E₃ => T y (fun j => EuclideanSpace.basisFun (Fin 3) ℝ
    (Function.update (fun l => a l.succ) i k j)))
    (M35.cylinderCoordinateEquiv.symm_apply_apply x)).symm

theorem cap_iteratedCovariantTensorDerivative_smooth
    {g : RiemannianMetric 3 E₃} (D : LeviCivitaData g) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r) (hT : IsSmoothCovariantTensor T)
    (k : ℕ) : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T k) := by
  induction k with
  | zero => exact hT
  | succ k ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih

end PoincareConjecture.M47

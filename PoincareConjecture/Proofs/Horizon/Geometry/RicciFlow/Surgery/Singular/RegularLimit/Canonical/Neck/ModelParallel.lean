import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

noncomputable section

namespace PoincareConjecture.SingularRegularLimit

def cylinderParallelCoefficient (A B : ℝ) (p : RoundCylinderCoordinates)
    (i j : Fin 3) : ℝ :=
  A * sphereFactor p * ⟪(roundCylinderCoordinateBasis i).1,
    (roundCylinderCoordinateBasis j).1⟫_ℝ +
    B * ((roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)

theorem cylinderParallelCoefficient_fderiv (A B : ℝ) (p : RoundCylinderCoordinates)
    (i j : Fin 3) :
    fderiv ℝ (fun p => cylinderParallelCoefficient A B p i j) p =
      (A * ⟪(roundCylinderCoordinateBasis i).1,
        (roundCylinderCoordinateBasis j).1⟫_ℝ) • fderiv ℝ sphereFactor p := by
  have heq : (fun p => cylinderParallelCoefficient A B p i j) =
      fun p => (A * ⟪(roundCylinderCoordinateBasis i).1,
        (roundCylinderCoordinateBasis j).1⟫_ℝ) * sphereFactor p +
        B * ((roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2) := by
    funext p
    dsimp only [cylinderParallelCoefficient]
    ring
  rw [heq, fderiv_add_const,
    fderiv_const_mul (sphereFactor_smooth.differentiable (by simp) p)]

private theorem cylinderParallelCoefficient_derivative_basis {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (A B : ℝ) (p : RoundCylinderCoordinates) (i j k : Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (fun p (a : Fin 2 → Fin 3) => cylinderParallelCoefficient A B p (a 0) (a 1))
      p ![i, j, k] = 0 := by
  have hp : sphereFactor p ≠ 0 := (sphereFactor_pos p).ne'
  simp only [roundCylinderTensorDerivative, roundCylinderChristoffel_time_eq hu]
  change (fderiv ℝ (fun r => cylinderParallelCoefficient A B r j k) p)
    (roundCylinderCoordinateBasis i) - _ = 0
  rw [cylinderParallelCoefficient_fderiv]
  simp only [roundCylinderChristoffel, cylinderGram_fderiv]
  rw [cylinderGram_inv_diagonal (by norm_num : (0 : ℝ) ≠ 1)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.diagonal, cylinderWeight, cylinderParallelCoefficient,
      roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left, sphereFactor_fderiv_axis]
    <;> field_simp <;> ring

theorem cylinderParallelCoefficient_derivative_zero {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (A B : ℝ) (p : RoundCylinderCoordinates) (a : Fin 3 → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (fun p (a : Fin 2 → Fin 3) => cylinderParallelCoefficient A B p (a 0) (a 1)) p a = 0 := by
  have ha : a = ![a 0, a 1, a 2] := by
    ext i
    fin_cases i <;> rfl
  rw [ha]
  exact cylinderParallelCoefficient_derivative_basis hu q A B p _ _ _

theorem roundCylinder_scaled_model_zeroth (u v c : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a : Fin 2 → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (fun z x y => c * EvolvingRoundCylinderMetric v z x y) 0 p a =
      cylinderParallelCoefficient (2 * c * (1 - v) - 2 * (1 - u)) (c - 1) p (a 0) (a 1) := by
  change c * roundCylinderGram v (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 0) (a 1) -
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 0) (a 1) = _
  rw [roundCylinderGram_eq_stereographic_formula, roundCylinderGram_eq_stereographic_formula]
  dsimp only [cylinderParallelCoefficient, sphereFactor]
  ring

theorem roundCylinder_scaled_model_positive_jet_zero {u : ℝ} (hu : u ≠ 1)
    (v c : ℝ) (q : UnitTwoSphere) (k : ℕ)
    (p : RoundCylinderCoordinates) (a : Fin (2 + (k + 1)) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (fun z x y => c * EvolvingRoundCylinderMetric v z x y) (k + 1) p a = 0 := by
  induction k generalizing p with
  | zero =>
      change roundCylinderTensorDerivative u _
        (roundCylinderIteratedDerivative u _ _ 0) p a = 0
      have heq := funext fun p => funext fun a => roundCylinder_scaled_model_zeroth u v c q p a
      rw [heq]
      exact cylinderParallelCoefficient_derivative_zero hu q _ _ p a
  | succ k ih =>
      change roundCylinderTensorDerivative u _
        (roundCylinderIteratedDerivative u _ _ (k + 1)) p a = 0
      have heq : roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (fun z x y => c * EvolvingRoundCylinderMetric v z x y) (k + 1) = fun _ _ => 0 := by
        funext p a
        exact ih p a
      rw [heq]
      simp [roundCylinderTensorDerivative]

end PoincareConjecture.SingularRegularLimit

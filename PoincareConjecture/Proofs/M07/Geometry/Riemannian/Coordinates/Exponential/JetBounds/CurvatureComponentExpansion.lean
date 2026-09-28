import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ConnectionKernel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.CoordinateExponential

open Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem radialCurvatureComponent_eq_sum_basis
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin (4 + m)) :
    radialCurvatureComponent D m v x =
      ∑ a, b.repr (v i) a * radialCurvatureComponent D m (Function.update v i (b a)) x := by
  classical
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 x
  have he : T x (v i) = ∑ a, b.repr (v i) a • T x (b a) := by
    simpa only [map_sum, map_smul] using congrArg (T x) (b.sum_repr (v i)).symm
  have h := congrArg (fun w => A (Function.update (fun j => T x (v j)) i w)) he
  simp only [Function.update_eq_self, MultilinearMap.map_update_sum,
    MultilinearMap.map_update_smul, smul_eq_mul] at h
  simp only [radialCurvatureComponent, ← hTv, hA]
  refine h.trans (Finset.sum_congr rfl fun a _ => ?_)
  congr 2
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem radialCurvatureComponent_four_eq_sum_two
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x u v w z : EuclideanSpace ℝ (Fin n)) :
    radialCurvatureComponent D 0 ![u, v, w, z] x =
      ∑ i, ∑ k, b.repr u i * (b.repr v k *
        radialCurvatureComponent D 0 ![b i, b k, w, z] x) := by
  classical
  have hfirst (a) : Function.update ![u, v, w, z] (0 : Fin 4) (b a) = ![b a, v, w, z] := by
    ext j
    fin_cases j <;> simp
  have hsecond (a k) : Function.update ![b a, v, w, z] (1 : Fin 4) (b k) =
      ![b a, b k, w, z] := by
    ext j
    fin_cases j <;> simp
  rw [radialCurvatureComponent_eq_sum_basis D b hTv 0 ![u, v, w, z] x 0]
  simp only [Matrix.cons_val_zero, hfirst]
  apply Finset.sum_congr rfl
  intro a _
  rw [radialCurvatureComponent_eq_sum_basis D b hTv 0 ![b a, v, w, z] x 1]
  simp only [Matrix.cons_val_one, hsecond, Finset.mul_sum]
  rfl

theorem radialCurvatureComponent_four_eq_sum_velocity
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    radialCurvatureComponent D 0 ![u, v, w, v] x =
      ∑ i, ∑ k, b.repr v i * (b.repr v k *
        radialCurvatureComponent D 0 ![u, b i, w, b k] x) := by
  classical
  have hfirst (a) : Function.update ![u, v, w, v] (1 : Fin 4) (b a) = ![u, b a, w, v] := by
    ext j
    fin_cases j <;> simp
  have hsecond (a k) : Function.update ![u, b a, w, v] (3 : Fin 4) (b k) =
      ![u, b a, w, b k] := by
    ext j
    fin_cases j <;> simp
  rw [radialCurvatureComponent_eq_sum_basis D b hTv 0 ![u, v, w, v] x 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hfirst]
  apply Finset.sum_congr rfl
  intro a _
  rw [radialCurvatureComponent_eq_sum_basis D b hTv 0 ![u, b a, w, v] x 3]
  simp only [Matrix.cons_val_three, hsecond, Finset.mul_sum]
  rfl

end PoincareConjecture.CoordinateExponential

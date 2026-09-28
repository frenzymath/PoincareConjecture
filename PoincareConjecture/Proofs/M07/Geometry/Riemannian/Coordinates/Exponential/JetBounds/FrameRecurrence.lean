import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialCurvature












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.CoordinateExponential

open Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem eq_sum_radial_frame
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x w : EuclideanSpace ℝ (Fin n)) :
    w = ∑ a, b.repr ((T x).inverse w) a •
      field (christoffelBilinear g.euclideanCoefficients) (b a) x := by
  have h := congrArg (T x) (b.sum_repr ((T x).inverse w))
  rw [(hTi x).self_apply_inverse] at h
  simp only [map_sum, map_smul] at h
  simpa only [hTv] using h.symm

private theorem multilinear_eq_sum_radial_frame
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    {k : ℕ} (A : MultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (V : Fin k → EuclideanSpace ℝ (Fin n)) (i : Fin k) :
    A V = ∑ a, b.repr ((T x).inverse (V i)) a *
      A (Function.update V i (field (christoffelBilinear g.euclideanCoefficients) (b a) x)) := by
  classical
  have h := congrArg (fun w => A (Function.update V i w))
    (eq_sum_radial_frame b hTi hTv x (V i))
  simpa only [Function.update_eq_self, MultilinearMap.map_update_sum,
    MultilinearMap.map_update_smul, smul_eq_mul] using h



theorem fderiv_radialCurvatureComponent_eq_frame_sum
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x d : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (radialCurvatureComponent D m v) x d =
      (∑ a, b.repr ((T x).inverse d) a *
        radialCurvatureComponent D (m + 1) (Fin.cons (b a) v) x) +
      ∑ i, ∑ a, b.repr ((T x).inverse
        (covariantDerivative (christoffelBilinear g.euclideanCoefficients)
          (field (christoffelBilinear g.euclideanCoefficients) (v i)) x d)) a *
        radialCurvatureComponent D m (Function.update v i (b a)) x := by
  classical
  rw [fderiv_radialCurvatureComponent]
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 x
  obtain ⟨B, hB⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model (m + 1)).1 x
  congr 1
  · have h := multilinear_eq_sum_radial_frame b hTi hTv B x
      (Fin.cons d (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) x)) 0
    simp only [Fin.cons_zero, Fin.update_cons_zero] at h
    simp only [radialCurvatureComponent, hB]
    refine h.trans (Finset.sum_congr rfl fun a _ => ?_)
    congr 2
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  · apply Finset.sum_congr rfl
    intro i _
    let V : Fin (4 + m) → EuclideanSpace ℝ (Fin n) :=
      fun j => field (christoffelBilinear g.euclideanCoefficients) (v j) x
    let w : EuclideanSpace ℝ (Fin n) :=
      covariantDerivative (christoffelBilinear g.euclideanCoefficients)
        (field (christoffelBilinear g.euclideanCoefficients) (v i)) x d
    change D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
      (Function.update V i w) = _
    refine (hA _).trans ((multilinear_eq_sum_radial_frame b hTi hTv A x
      (Function.update V i w) i).trans ?_)
    apply Finset.sum_congr rfl
    intro a _
    simp only [Function.update_self, Function.update_idem, radialCurvatureComponent, hA]
    congr 2
    funext j
    by_cases hj : j = i <;> simp [hj, V]

end PoincareConjecture.CoordinateExponential

import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameJetBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open ConnectionVariation CoordinateExponential LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

def coordinateCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  D.iteratedCovariantTensorDerivative D.riemannEvaluation m x v

theorem contDiff_coordinateCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (coordinateCurvatureComponent D m v) := by
  let hC := D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m
  have hS : ContDiff ℝ ∞ (LeviCivitaData.tensorCoordinateSection hC
      (0 : EuclideanSpace ℝ (Fin n))) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using
      LeviCivitaData.contDiffAt_tensorCoordinateSection hC
        (0 : EuclideanSpace ℝ (Fin n)) (z := x) (by simp)
  have he := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin n)) (k := 4 + m)).analyticOnNhd_uncurry_of_multilinear
    (s := Set.univ) |>.contDiff (n := ∞)
  change ContDiff ℝ ∞ (fun x => D.iteratedCovariantTensorDerivative
    D.riemannEvaluation m x v)
  simpa only [Function.comp_def, TensorFiber.continuousMultilinear_apply,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model, coordinateCurvatureComponent] using
    he.comp (hS.prodMk (contDiff_const (c := v)))

theorem fderiv_coordinateCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x d : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (coordinateCurvatureComponent D m v) x d =
      coordinateCurvatureComponent D (m + 1) (Fin.cons d v) x +
        ∑ i, coordinateCurvatureComponent D m
          (Function.update v i (christoffelBilinear g.euclideanCoefficients x d (v i))) x := by
  unfold coordinateCurvatureComponent
  have h := D.fderiv_covariantTensor_pullback_model
    (D.iteratedCovariantTensorDerivative_isSmooth D.riemannEvaluation_isSmooth_model m)
    (q := id) (V := fun i _ => v i) (p := x) differentiableAt_id
    (fun _ => differentiableAt_const _) d
  simpa [coordinateCurvatureComponent, LeviCivitaData.iteratedCovariantTensorDerivative,
    manifoldCovDerivAlong_model, covDerivAlong_def] using h

private theorem component_update_eq_sum (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin (4 + m)) (w : EuclideanSpace ℝ (Fin n)) :
    coordinateCurvatureComponent D m (Function.update v i w) x =
      ∑ a, b.repr w a * coordinateCurvatureComponent D m (Function.update v i (b a)) x := by
  classical
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 x
  have h := congrArg (fun z => A (Function.update v i z)) (b.sum_repr w).symm
  simpa only [coordinateCurvatureComponent, hA, MultilinearMap.map_update_sum,
    MultilinearMap.map_update_smul, smul_eq_mul] using h

theorem fderiv_coordinateCurvatureComponent_eq_sum (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (m : ℕ) (J : Fin (4 + m) → Fin n) (x d : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (coordinateCurvatureComponent D m (fun j => b (J j))) x d =
      (∑ a, b.repr d a *
        coordinateCurvatureComponent D (m + 1)
          (fun j => b ((Fin.cons a J : Fin ((4 + m) + 1) → Fin n) j)) x) +
      ∑ i, ∑ a, b.repr (christoffelBilinear g.euclideanCoefficients x d (b (J i))) a *
        coordinateCurvatureComponent D m (fun j => b (Function.update J i a j)) x := by
  classical
  rw [fderiv_coordinateCurvatureComponent]
  congr 1
  · have h := component_update_eq_sum D b (m + 1)
      (Fin.cons d (fun j => b (J j))) x 0 d
    simp only [Fin.update_cons_zero] at h
    refine h.trans (Finset.sum_congr rfl fun a _ => ?_)
    congr 2
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [component_update_eq_sum D b]
    apply Finset.sum_congr rfl
    intro a _
    congr 2
    funext j
    by_cases hj : j = i <;> simp [hj]

end PoincareConjecture.SpacetimeBounds

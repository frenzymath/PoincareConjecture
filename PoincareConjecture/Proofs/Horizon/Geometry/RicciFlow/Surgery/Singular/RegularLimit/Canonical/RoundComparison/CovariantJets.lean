import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n k : ℕ} {ι : Type*} {l : Filter ι}
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem tendsto_multilinear_zero_of_apply
    {A : ι → ContinuousMultilinearMap ℝ
      (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ}
    (hA : ∀ v, Tendsto (fun i => A i v) l (𝓝 0)) :
    Tendsto A l (𝓝 0) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  apply squeeze_zero_norm (a := fun i =>
    Real.sqrt (∑ a : Fin k → Fin n, (A i (fun r => b (a r))) ^ 2))
  · intro i
    apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
    intro v
    exact abs_multilinear_apply_le_orthonormal_tensor_norm
      (A i).toMultilinearMap b v
  · have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin n))
      (fun a _ => (hA (fun r => b (a r))).pow 2)
    simp only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hsum
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsum


theorem tendsto_tensor_apply_zero
    {T : ι → CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin n))
    (h : Tendsto (fun i => g.tensorNorm (T i) x) l (𝓝 0))
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun i => T i x v) l (𝓝 0) := by
  apply squeeze_zero_norm (a := fun i =>
    g.tensorNorm (T i) x * ∏ r, g.tangentNorm x (v r))
  · intro i
    obtain ⟨A, hA⟩ := (hT i).1 x
    exact abs_tensor_evaluation_le_tensorNorm g (T i) x A hA v
  · simpa using h.mul_const (∏ r, g.tangentNorm x (v r))

private theorem contDiffAt_tensor_apply_model
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n))
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun y => T y v) x := by
  have h := (TensorFiber.evaluation v).contDiff.contDiffAt.comp x
    (LeviCivitaData.contDiffAt_tensorCoordinateSection hT
      (0 : EuclideanSpace ℝ (Fin n)) (by simp : x ∈
        (extChartAt (𝓡 n) (0 : EuclideanSpace ℝ (Fin n))).target))
  simpa only [Function.comp_def, TensorFiber.evaluation_apply,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq] using h



theorem tendsto_fderiv_tensor_apply_zero
    (D : LeviCivitaData g)
    {T : ι → CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => g.tensorNorm (T i) x) l (𝓝 0))
    (hone : Tendsto (fun i => g.tensorNorm
      (D.covariantTensorDerivative (T i)) x) l (𝓝 0))
    (V : Fin k → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hV : ∀ j, DifferentiableAt ℝ (V j) x)
    (a : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun i => fderiv ℝ (fun y => T i y (fun j => V j y)) x a)
      l (𝓝 0) := by
  classical
  have hfirst := tendsto_tensor_apply_zero
    (fun i => D.covariantTensorDerivative_isSmooth (hT i)) x hone
    (Fin.cons a (fun j => V j x))
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_tensor_apply_zero hT x hzero
      (Function.update (fun r => V r x) j
        (ConnectionVariation.manifoldCovDerivAlong g id (V j) a x)))
  have heq (i : ι) := D.fderiv_covariantTensor_pullback_model
    (hT i) (q := id) (p := x) differentiableAt_id hV a
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] at heq
  simp_rw [heq]
  simpa using hfirst.add hsum

private theorem differentiableAt_tensor_apply_model
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n))
    (V : Fin k → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hV : ∀ j, DifferentiableAt ℝ (V j) x) :
    DifferentiableAt ℝ (fun y => T y (fun j => V j y)) x := by
  let S := fun y => LeviCivitaData.tensorCoordinateSection hT
    (0 : EuclideanSpace ℝ (Fin n)) y
  have hS : DifferentiableAt ℝ S x := by
    have h := LeviCivitaData.contDiffAt_tensorCoordinateSection hT
      (0 : EuclideanSpace ℝ (Fin n)) (by simp : x ∈
        (extChartAt (𝓡 n) (0 : EuclideanSpace ℝ (Fin n))).target)
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using h.differentiableAt (by simp)
  have hC := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin n)) (k := k)).hasFDerivAt.comp x hS.hasFDerivAt
  have h := (hC.continuousMultilinearMap_apply (fun j => (hV j).hasFDerivAt)).differentiableAt
  simpa only [Function.comp_apply, TensorFiber.continuousMultilinear_apply, S,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model] using h



theorem tendsto_iteratedFDeriv_tensor_apply_zero
    (D : LeviCivitaData g)
    {T : ι → CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 2 → Tendsto (fun i =>
      g.tensorNorm (D.iteratedCovariantTensorDerivative (T i) r) x) l (𝓝 0))
    (r : ℕ) (hr : r ≤ 2) (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fun y => T i y v) x) l (𝓝 0) := by
  classical
  have hzero := hjets 0 (by omega)
  have hone := hjets 1 (by omega)
  have htwo := hjets 2 (by omega)
  change Tendsto (fun i => g.tensorNorm (T i) x) l (𝓝 0) at hzero
  change Tendsto (fun i => g.tensorNorm (D.covariantTensorDerivative (T i)) x)
    l (𝓝 0) at hone
  change Tendsto (fun i => g.tensorNorm
    (D.covariantTensorDerivative (D.covariantTensorDerivative (T i))) x)
    l (𝓝 0) at htwo
  apply tendsto_multilinear_zero_of_apply
  intro w
  interval_cases r
  · simpa only [iteratedFDeriv_zero_apply] using tendsto_tensor_apply_zero hT x hzero v
  · simpa only [iteratedFDeriv_one_apply] using
      tendsto_fderiv_tensor_apply_zero D hT x hzero hone
        (fun j _ => v j) (fun _ => differentiableAt_const _) (w 0)
  · let a := w 0
    let b := w 1
    let Γ := CoordinateExponential.christoffelBilinear g.euclideanCoefficients
    let W := fun j : Fin k => fun s : Fin k =>
      fun y : EuclideanSpace ℝ (Fin n) => Function.update v j (Γ y b (v j)) s
    have hΓ : ContDiff ℝ ∞ Γ := contDiff_iff_contDiffAt.mpr fun y =>
      CoordinateExponential.contDiffAt_christoffelBilinear
        (g.contDiffAt_euclideanCoefficients y) (g.inner_isInvertible y)
    have hW (j s : Fin k) : DifferentiableAt ℝ (W j s) x := by
      by_cases hsj : s = j
      · subst s
        simpa only [W, Function.update_self] using
          ((hΓ.contDiffAt.clm_apply contDiffAt_const).clm_apply
            contDiffAt_const).differentiableAt (by simp)
      · simpa only [W, Function.update_of_ne hsj] using
          (differentiableAt_const (v s) : DifferentiableAt ℝ (fun _ => v s) x)
    have heq (i : ι) :
        (fun y => fderiv ℝ (fun z => T i z v) y b) =
          fun y => D.covariantTensorDerivative (T i) y (Fin.cons b v) +
            ∑ j : Fin k, T i y (fun s => W j s y) := by
      funext y
      have h := D.fderiv_covariantTensor_pullback_model (hT i)
        (q := id) (p := y) differentiableAt_id
        (V := fun j _ => v j) (fun _ => differentiableAt_const _) b
      simpa only [id_eq, fderiv_id, ContinuousLinearMap.id_apply,
        LeviCivitaData.manifoldCovDerivAlong_model,
        ConnectionVariation.covDerivAlong_def, fderiv_const_apply,
        zero_apply, zero_add, W, Γ] using h
    have hDfirst (i : ι) : DifferentiableAt ℝ
        (fun y => D.covariantTensorDerivative (T i) y (Fin.cons b v)) x :=
      (contDiffAt_tensor_apply_model (D.covariantTensorDerivative_isSmooth (hT i))
        x (Fin.cons b v)).differentiableAt (by simp)
    have hDsum (i : ι) (j : Fin k) :
        DifferentiableAt ℝ (fun y => T i y (fun s => W j s y)) x :=
      differentiableAt_tensor_apply_model (hT i) x (W j) (hW j)
    have hfirst := tendsto_fderiv_tensor_apply_zero (k := k + 1) D
      (T := fun i => D.covariantTensorDerivative (T i))
      (fun i => D.covariantTensorDerivative_isSmooth (hT i)) x hone htwo
      (fun j _ => (Fin.cons b v : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) j)
      (by intro j; exact differentiableAt_const _) a
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
      tendsto_fderiv_tensor_apply_zero D hT x hzero hone (W j) (hW j) a)
    have hsecond (i : ι) :
        iteratedFDeriv ℝ 2 (fun y => T i y v) x w =
          fderiv ℝ (fun y => D.covariantTensorDerivative (T i) y
            (Fin.cons b v)) x a +
          ∑ j : Fin k, fderiv ℝ (fun y => T i y (fun s => W j s y)) x a := by
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (fun y => T i y v)) x :=
        ((contDiffAt_tensor_apply_model (hT i) x v).iteratedFDeriv_right
          (m := ∞) (by simp)).differentiableAt (by simp)
      rw [hd.iteratedFDeriv_succ_apply_left' (m := w)]
      simp only [iteratedFDeriv_one_apply]
      change fderiv ℝ (fun y => fderiv ℝ (fun z => T i z v) y b) x a = _
      rw [heq, fderiv_fun_add (hDfirst i) (DifferentiableAt.fun_sum
        (fun j _ => hDsum i j)), fderiv_fun_sum (fun j _ => hDsum i j)]
      simp only [add_apply, sum_apply]
    simp_rw [hsecond]
    simpa using hfirst.add hsum

end PoincareConjecture.SingularRegularLimit.RoundComparison

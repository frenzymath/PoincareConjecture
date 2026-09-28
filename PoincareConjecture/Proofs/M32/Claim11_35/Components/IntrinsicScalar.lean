import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedSpatialContact

















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M32

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem intrinsic_tendsto_multilinear_zero
    {k : ℕ} {ι : Type*} {l : Filter ι}
    {A : ι → ContinuousMultilinearMap ℝ
      (fun _ : Fin k => EuclideanSpace ℝ (Fin 3)) ℝ}
    (hA : ∀ v, Tendsto (fun i => A i v) l (𝓝 0)) :
    Tendsto A l (𝓝 0) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  apply squeeze_zero_norm (a := fun i =>
    Real.sqrt (∑ a : Fin k → Fin 3, (A i (fun r => b (a r))) ^ 2))
  · intro i
    apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
    intro v
    exact abs_multilinear_apply_le_orthonormal_tensor_norm
      (A i).toMultilinearMap b v
  · have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin 3))
      (fun a _ => (hA (fun r => b (a r))).pow 2)
    simp only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hsum
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsum

private theorem intrinsic_tendsto_tensor_apply_zero
    {k : ℕ} {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    {T : ι → CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin 3))
    (h : Tendsto (fun i => g.tensorNorm (T i) x) l (𝓝 0))
    (v : Fin k → EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun i => T i x v) l (𝓝 0) := by
  apply squeeze_zero_norm (a := fun i =>
    g.tensorNorm (T i) x * ∏ r, g.tangentNorm x (v r))
  · intro i
    obtain ⟨A, hA⟩ := (hT i).1 x
    exact abs_tensor_evaluation_le_tensorNorm g (T i) x A hA v
  · simpa using h.mul_const (∏ r, g.tangentNorm x (v r))

private theorem intrinsic_contDiffAt_tensor_apply
    {k : ℕ} {T : CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) k}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin 3))
    (v : Fin k → EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ ∞ (fun y => T y v) x := by
  have h := (TensorFiber.evaluation v).contDiff.contDiffAt.comp x
    (LeviCivitaData.contDiffAt_tensorCoordinateSection hT
      (0 : EuclideanSpace ℝ (Fin 3)) (by simp : x ∈
        (extChartAt (𝓡 3) (0 : EuclideanSpace ℝ (Fin 3))).target))
  simpa only [Function.comp_def, TensorFiber.evaluation_apply,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq] using h

private theorem intrinsic_tendsto_fderiv_tensor_apply_zero
    {k : ℕ} {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    {T : ι → CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin 3))
    (hzero : Tendsto (fun i => g.tensorNorm (T i) x) l (𝓝 0))
    (hone : Tendsto (fun i => g.tensorNorm
      (D.covariantTensorDerivative (T i)) x) l (𝓝 0))
    (V : Fin k → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ j, DifferentiableAt ℝ (V j) x)
    (a : EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun i => fderiv ℝ (fun y => T i y (fun j => V j y)) x a)
      l (𝓝 0) := by
  classical
  have hfirst := intrinsic_tendsto_tensor_apply_zero
    (fun i => D.covariantTensorDerivative_isSmooth (hT i)) x hone
    (Fin.cons a (fun j => V j x))
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    intrinsic_tendsto_tensor_apply_zero hT x hzero
      (Function.update (fun r => V r x) j
        (ConnectionVariation.manifoldCovDerivAlong g id (V j) a x)))
  have heq (i : ι) := D.fderiv_covariantTensor_pullback_model
    (hT i) (q := id) (p := x) differentiableAt_id hV a
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] at heq
  simp_rw [heq]
  simpa using hfirst.add hsum

private theorem intrinsic_differentiableAt_tensor_apply
    {k : ℕ} {T : CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) k}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin 3))
    (V : Fin k → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ j, DifferentiableAt ℝ (V j) x) :
    DifferentiableAt ℝ (fun y => T y (fun j => V j y)) x := by
  let S := fun y => LeviCivitaData.tensorCoordinateSection hT
    (0 : EuclideanSpace ℝ (Fin 3)) y
  have hS : DifferentiableAt ℝ S x := by
    have h := LeviCivitaData.contDiffAt_tensorCoordinateSection hT
      (0 : EuclideanSpace ℝ (Fin 3)) (by simp : x ∈
        (extChartAt (𝓡 3) (0 : EuclideanSpace ℝ (Fin 3))).target)
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using h.differentiableAt (by simp)
  have hC := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin 3)) (k := k)).hasFDerivAt.comp x hS.hasFDerivAt
  have h := (hC.continuousMultilinearMap_apply (fun j => (hV j).hasFDerivAt)).differentiableAt
  simpa only [Function.comp_apply, TensorFiber.continuousMultilinear_apply, S,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model] using h

private theorem intrinsic_tendsto_iteratedFDeriv_tensor_apply_zero
    {k : ℕ} {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    {T : ι → CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) k}
    (hT : ∀ i, IsSmoothCovariantTensor (T i))
    (x : EuclideanSpace ℝ (Fin 3))
    (hjets : ∀ r : ℕ, r ≤ 2 → Tendsto (fun i =>
      g.tensorNorm (D.iteratedCovariantTensorDerivative (T i) r) x) l (𝓝 0))
    (r : ℕ) (hr : r ≤ 2) (v : Fin k → EuclideanSpace ℝ (Fin 3)) :
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
  apply intrinsic_tendsto_multilinear_zero
  intro w
  interval_cases r
  · simpa only [iteratedFDeriv_zero_apply] using
      intrinsic_tendsto_tensor_apply_zero hT x hzero v
  · simpa only [iteratedFDeriv_one_apply] using
      intrinsic_tendsto_fderiv_tensor_apply_zero D hT x hzero hone
        (fun j _ => v j) (fun _ => differentiableAt_const _) (w 0)
  · let a := w 0
    let b := w 1
    let Γ := CoordinateExponential.christoffelBilinear g.euclideanCoefficients
    let W := fun j : Fin k => fun s : Fin k =>
      fun y : EuclideanSpace ℝ (Fin 3) => Function.update v j (Γ y b (v j)) s
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
      (intrinsic_contDiffAt_tensor_apply (D.covariantTensorDerivative_isSmooth (hT i))
        x (Fin.cons b v)).differentiableAt (by simp)
    have hDsum (i : ι) (j : Fin k) :
        DifferentiableAt ℝ (fun y => T i y (fun s => W j s y)) x :=
      intrinsic_differentiableAt_tensor_apply (hT i) x (W j) (hW j)
    have hfirst := intrinsic_tendsto_fderiv_tensor_apply_zero (k := k + 1) D
      (T := fun i => D.covariantTensorDerivative (T i))
      (fun i => D.covariantTensorDerivative_isSmooth (hT i)) x hone htwo
      (fun j _ => (Fin.cons b v : Fin (k + 1) → EuclideanSpace ℝ (Fin 3)) j)
      (by intro j; exact differentiableAt_const _) a
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
      intrinsic_tendsto_fderiv_tensor_apply_zero D hT x hzero hone (W j) (hW j) a)
    have hsecond (i : ι) :
        iteratedFDeriv ℝ 2 (fun y => T i y v) x w =
          fderiv ℝ (fun y => D.covariantTensorDerivative (T i) y
            (Fin.cons b v)) x a +
          ∑ j : Fin k, fderiv ℝ (fun y => T i y (fun s => W j s y)) x a := by
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (fun y => T i y v)) x :=
        ((intrinsic_contDiffAt_tensor_apply (hT i) x v).iteratedFDeriv_right
          (m := ∞) (by simp)).differentiableAt (by simp)
      rw [hd.iteratedFDeriv_succ_apply_left' (m := w)]
      simp only [iteratedFDeriv_one_apply]
      change fderiv ℝ (fun y => fderiv ℝ (fun z => T i z v) y b) x a = _
      rw [heq, fderiv_fun_add (hDfirst i) (DifferentiableAt.fun_sum
        (fun j _ => hDsum i j)), fderiv_fun_sum (fun j _ => hDsum i j)]
      simp only [add_apply, sum_apply]
    simp_rw [hsecond]
    simpa using hfirst.add hsum

private theorem intrinsic_tendsto_scalar_of_jets
    {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData g)
    {h : ι → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (DH : ∀ i, LeviCivitaData (h i)) (x : EuclideanSpace ℝ (Fin 3))
    (hjets : ∀ r : ℕ, r ≤ 2 → Tendsto (fun i => g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → EuclideanSpace ℝ (Fin 3)) =>
          (h i).inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) x)
      l (𝓝 0)) :
    Tendsto (fun i => (DH i).scalarCurvature x) l (𝓝 (D.scalarCurvature x)) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  apply LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets DH D x b
  intro r hr a c
  have he := intrinsic_tendsto_iteratedFDeriv_tensor_apply_zero D
    (fun i => (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor (h i)).sub
      (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g)) x hjets r hr ![b a, b c]
  have hsm (g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) :
      ContDiffAt ℝ r (fun y => g'.inner y (b a) (b c)) x := by
    have hs : ContDiffAt ℝ ∞ (fun y => g'.inner y (b a) (b c)) x :=
      ((g'.contDiffAt_euclideanCoefficients x).clm_apply
        contDiffAt_const).clm_apply contDiffAt_const
    exact hs.of_le (by norm_cast; exact le_top)
  have hid (i : ι) :
      iteratedFDeriv ℝ r (fun y => (h i).inner y (b a) (b c) - g.inner y (b a) (b c)) x =
        iteratedFDeriv ℝ r (fun y => (h i).inner y (b a) (b c)) x -
          iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x :=
    fun_iteratedFDeriv_sub_apply (hsm (h i)) (hsm g)
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  simp_rw [hid] at he
  simpa only [sub_add_cancel, zero_add] using he.add_const
    (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)





theorem exists_scalar_control_of_covariant_metric_twoJet
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin 3))
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DH : LeviCivitaData h),
        (∀ r : ℕ, r ≤ 2 → g.tensorNorm
          (D.iteratedCovariantTensorDerivative
            (fun y (v : Fin 2 → EuclideanSpace ℝ (Fin 3)) =>
              h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) x < delta) →
        |DH.scalarCurvature x - D.scalarCurvature x| < alpha := by
  let Data := (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) × LeviCivitaData h
  let J : Data → Fin 3 → ℝ := fun p r => g.tensorNorm
    (D.iteratedCovariantTensorDerivative
      (fun y (v : Fin 2 → EuclideanSpace ℝ (Fin 3)) =>
        p.1.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r.val) x
  let L := Filter.comap J (𝓝 0)
  have hJ : Tendsto J L (𝓝 0) := tendsto_comap
  have hjets (r : ℕ) (hr : r ≤ 2) : Tendsto (fun p : Data => g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → EuclideanSpace ℝ (Fin 3)) =>
          p.1.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) x) L (𝓝 0) := by
    exact ((continuous_apply (⟨r, by omega⟩ : Fin 3)).tendsto 0).comp hJ
  have hscalar := intrinsic_tendsto_scalar_of_jets D (fun p : Data => p.2) x hjets
  obtain ⟨delta, hdelta, hbound⟩ := (Metric.nhds_basis_ball.comap J).mem_iff.mp
    (hscalar (Metric.ball_mem_nhds (D.scalarCurvature x) halpha))
  refine ⟨delta, hdelta, fun h DH hclose => ?_⟩
  have hJclose : J ⟨h, DH⟩ ∈ Metric.ball 0 delta := by
    rw [Metric.mem_ball, dist_pi_lt_iff hdelta]
    intro r
    simpa only [Real.dist_eq, Pi.zero_apply, sub_zero, J,
      RiemannianMetric.tensorNorm, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hclose r.val (by omega)
  simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hbound hJclose

end PoincareConjecture.M32

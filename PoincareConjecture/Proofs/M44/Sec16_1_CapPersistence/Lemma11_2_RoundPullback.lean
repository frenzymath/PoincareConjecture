import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_IntrinsicJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Algebra










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M44

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]




theorem isSmoothCovariantTensor_metric_pullback (g : RiemannianMetric n N)
    {f : M → N} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) :
    IsSmoothCovariantTensor (k := 2) (fun x v =>
      g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x (v 0))
        (mfderiv (𝓡 n) (𝓡 n) f x (v 1))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro x
    refine ⟨MultilinearMap.mk' (R := ℝ) _ ?_ ?_, fun _ => rfl⟩
    · intro v i a b
      fin_cases i <;> simp [map_add]
    · intro v i r a
      fin_cases i <;> simp [map_smul]
  · intro U hU X hX x hx
    have hV (i : Fin 2) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f y)
          (mfderiv (𝓡 n) (𝓡 n) f y (X i y))) x :=
      ((hf x).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
        ((hX i).contMDiffAt (hU.mem_nhds hx)) (hf x)
    exact ((hV 0).inner_bundle (hV 1)).contMDiffWithinAt



theorem isSmoothCovariantTensor_metric (g : RiemannianMetric n M) :
    IsSmoothCovariantTensor (k := 2) (fun x v => g.inner x (v 0) (v 1)) := by
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
    isSmoothCovariantTensor_metric_pullback g (f := id) contMDiff_id




theorem tensorNorm_iterated_eq_of_metric_pullback
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {k : ℕ} {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n N k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hST : ∀ y ∈ U, ∀ v,
      S y v = T (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i)))
    (m : ℕ) {x : M} (hx : x ∈ U) :
    g.tensorNorm (D.iteratedCovariantTensorDerivative S m) x =
      h.tensorNorm (D'.iteratedCovariantTensorDerivative T m) (f x) := by
  obtain ⟨e, he⟩ := hinv x hx
  have he' (v : TangentSpace (𝓡 n) x) : e v = mfderiv (𝓡 n) (𝓡 n) f x v :=
    congrArg (fun L => L v) he
  obtain ⟨A, hA⟩ := (D'.iteratedCovariantTensorDerivative_isSmooth hT m).1 (f x)
  apply g.tensorNorm_eq_of_linearEquiv h _ _ x (f x) e.toLinearEquiv _ _ A hA
  · intro u v
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, he',
      ContinuousLinearEquiv.coe_coe] using (hmetric x hx u v).symm
  · intro v
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, he',
      ContinuousLinearEquiv.coe_coe] using
      D.iteratedCovariantTensorDerivative_eq_pullback D' hU hf hinv hmetric hS hT hST m hx v




theorem round_error_isSmooth {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon) :
    IsSmoothCovariantTensor (fun y v => R.scale * singularMetricPullback g R.forward y v -
      R.model_metric.inner y (v 0) (v 1)) :=
  ((isSmoothCovariantTensor_metric_pullback g R.forward_smooth).const_mul R.scale).sub
    (isSmoothCovariantTensor_metric R.model_metric)



theorem round_covariant_error_lt {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon)
    {j : ℕ} (hj : j ≤ ⌊epsilon⁻¹⌋₊) (x : R.model.carrier) :
    R.model_metric.tensorNorm (R.model_connection.iteratedCovariantTensorDerivative
      (fun y v => R.scale * singularMetricPullback g R.forward y v -
        R.model_metric.inner y (v 0) (v 1)) j) x < epsilon := by
  obtain ⟨B, hB, hjet⟩ := R.metric_comparison
  exact metric_covariant_error_lt_of_jet_error R.model_metric R.model_connection
    (fun y v => R.scale * singularMetricPullback g R.forward y v) hj R.epsilon_pos
    ((hjet x).trans_lt hB)




theorem round_quadratic_bounds {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon)
    (x : R.model.carrier) (v : TangentSpace (𝓡 3) x) :
    (1 - epsilon) * R.model_metric.inner x v v ≤
        R.scale * g.inner (R.forward x) (mfderiv (𝓡 3) (𝓡 3) R.forward x v)
          (mfderiv (𝓡 3) (𝓡 3) R.forward x v) ∧
      R.scale * g.inner (R.forward x) (mfderiv (𝓡 3) (𝓡 3) R.forward x v)
        (mfderiv (𝓡 3) (𝓡 3) R.forward x v) ≤
          (1 + epsilon) * R.model_metric.inner x v v := by
  let T : CovariantTensorEvaluation 3 R.model.carrier 2 := fun y z =>
    R.scale * singularMetricPullback g R.forward y z -
      R.model_metric.inner y (z 0) (z 1)
  obtain ⟨A, hA⟩ := (round_error_isSmooth R).1 x
  have hn : R.model_metric.tensorNorm T x < epsilon :=
    round_covariant_error_lt R (Nat.zero_le _) x
  have hv : 0 ≤ R.model_metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (R.model_metric.pos x v hv).le
  have hp : (∏ i : Fin 2, R.model_metric.tangentNorm x (![v, v] i)) =
      R.model_metric.inner x v v := by
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      RiemannianMetric.tangentNorm, ← sq, Real.sq_sqrt hv]
  have hh := abs_tensor_evaluation_le_tensorNorm R.model_metric T x A hA ![v, v]
  rw [hp] at hh
  have hb := abs_le.mp (hh.trans (mul_le_mul_of_nonneg_right hn.le hv))
  dsimp only [T, singularMetricPullback, Matrix.cons_val_zero, Matrix.cons_val_one] at hb
  constructor <;> nlinarith [hb.1, hb.2]

end PoincareConjecture.M44

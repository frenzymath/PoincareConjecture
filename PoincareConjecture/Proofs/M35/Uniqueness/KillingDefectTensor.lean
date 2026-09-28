import PoincareConjecture.Proofs.M35.Uniqueness.KillingCovector
import PoincareConjecture.Proofs.M04.TensorLaplacianDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)

private theorem smooth_add {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (V n) M] [IsManifold (𝓡 n) ∞ M] {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun x v => S x v + T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    exact ⟨A + B, fun v => by simp only [hA, hB, add_apply]⟩
  · intro U hU X hX
    exact (hS.2 U hU X hX).add (hT.2 U hU X hX)

private theorem derivative_add {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (V n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.covariantTensorDerivative (fun x v => S x v + T x v) =
      fun x v => D.covariantTensorDerivative S x v + D.covariantTensorDerivative T x v := by
  funext x v
  let e := trivializationAt (V n) (TangentSpace (𝓡 n) : M → Type _) x
  let W := fun i : Fin k => FiberBundle.extend (V n) (v i.succ)
  have hW (i : Fin k) := M04.contMDiffOn_extend_baseSet (v i.succ)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hs := ((hS.2 e.baseSet e.open_baseSet W hW).contMDiffAt
    (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have ht := ((hT.2 e.baseSet e.open_baseSet W hW).contMDiffAt
    (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  dsimp only [W] at hs ht
  simp only [LeviCivitaData.covariantTensorDerivative, mvfderiv_fun_add hs ht,
    add_apply, Finset.sum_add_distrib]
  ring

private theorem laplacian_add {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (V n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.tensorLaplacian (fun x v => S x v + T x v) =
      fun x v => D.tensorLaplacian S x v + D.tensorLaplacian T x v := by
  funext x v
  simp only [LeviCivitaData.tensorLaplacian, LeviCivitaData.iteratedCovariantTensorDerivative,
    derivative_add D hS hT, derivative_add D
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hS)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hT), Finset.sum_add_distrib]


noncomputable def killingDefectTensor {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) : CovariantTensorEvaluation n (V n) 2 :=
  fun x v => DeTurckNative.metricLieDerivative D X x (v 0) (v 1)

private theorem defect_eq {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X) :
    killingDefectTensor D X = fun x v =>
      D.covariantTensorDerivative (killingCovector g X) x v +
        M04.tensorPermute (D.covariantTensorDerivative (killingCovector g X))
          (Equiv.swap (0 : Fin 2) 1) x v := by
  funext x v
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  have hs : v ∘ Equiv.swap (0 : Fin 2) 1 = ![v 1, v 0] := by
    ext i
    fin_cases i <;> simp
  change DeTurckNative.metricLieDerivative D X x (v 0) (v 1) = _
  rw [killing_defect_eq_covector_symmetrization D X hX, M04.tensorPermute, hs, hv]



theorem isSmoothCovariantTensor_killingDefectTensor {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) :
    IsSmoothCovariantTensor (killingDefectTensor D X) := by
  rw [defect_eq D X hX]
  have hK := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_killingCovector g X hX)
  exact smooth_add hK (M04.isSmoothCovariantTensor_tensorPermute hK _)



theorem killingDefectTensor_laplacian {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x a b : V n) :
    D.tensorLaplacian (killingDefectTensor D X) x ![a, b] =
      D.tensorLaplacian (D.covariantTensorDerivative (killingCovector g X)) x ![a, b] +
        D.tensorLaplacian (D.covariantTensorDerivative (killingCovector g X)) x ![b, a] := by
  let K := D.covariantTensorDerivative (killingCovector g X)
  let s := Equiv.swap (0 : Fin 2) 1
  have hK := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_killingCovector g X hX)
  have hs : ![a, b] ∘ s = ![b, a] := by
    ext i
    fin_cases i <;> simp [s]
  have hp : D.tensorLaplacian (M04.tensorPermute K s) x ![a, b] =
      D.tensorLaplacian K x ![b, a] := by
    unfold LeviCivitaData.tensorLaplacian
    apply Finset.sum_congr rfl
    intro i _
    simpa only [hs] using M04.secondCovariantTensorDerivative_tensorPermute D hK s x
      (g.orthonormalBasis x i) (g.orthonormalBasis x i) ![a, b]
  rw [defect_eq D X hX, laplacian_add D hK (M04.isSmoothCovariantTensor_tensorPermute hK s)]
  exact congrArg (fun r => D.tensorLaplacian K x ![a, b] + r) hp

end PoincareConjecture.M35.Uniqueness

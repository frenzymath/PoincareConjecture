import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Kato
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Powers

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem IsSmoothCovariantTensor.scalar_mul {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) :
    IsSmoothCovariantTensor (fun x v => φ x * T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨φ x • A, fun v => by simp only [hA, smul_apply, smul_eq_mul]⟩
  · intro U hU X hX
    exact hφ.contMDiffOn.mul (hT.2 U hU X hX)

namespace LeviCivitaData

theorem covariantTensorDerivative_scalar_mul (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {φ : M → ℝ} {x : M} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z => φ y * T y z) x v =
      mvfderiv (𝓡 n) φ x (v 0) * T x (fun i => v i.succ) +
        φ x * D.covariantTensorDerivative T x v := by
  have hTx := (hT.contMDiffAt_extend x (fun i => v i.succ)).mdifferentiableAt
    (by simp)
  have hd := mvfderiv_fun_mul hφ hTx
  simp only [covariantTensorDerivative, hd, add_apply, smul_apply, smul_eq_mul,
    FiberBundle.extend_apply_self, ← Finset.mul_sum]
  ring

theorem tensorPairingThree_derivative_scalar_mul_cross (D : LeviCivitaData g)
    (F : CovariantTensorEvaluation n M 3)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {φ : M → ℝ} {x : M} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x) :
    g.tensorPairingThree F
        (D.covariantTensorDerivative (fun y v => φ y * T y v)) x =
      φ x * g.tensorPairingThree F (D.covariantTensorDerivative T) x +
        ∑ a, mvfderiv (𝓡 n) φ x (g.orthonormalBasis x a) *
          g.tensorPairingCovector F T x ![g.orthonormalBasis x a] := by
  let e := g.orthonormalBasis x
  have hterm (a i j) :
      F x ![e a, e i, e j] *
          D.covariantTensorDerivative (fun y v => φ y * T y v) x ![e a, e i, e j] =
        φ x * (F x ![e a, e i, e j] *
          D.covariantTensorDerivative T x ![e a, e i, e j]) +
        mvfderiv (𝓡 n) φ x (e a) *
          (F x ![e a, e i, e j] * T x ![e i, e j]) := by
    have hd := D.covariantTensorDerivative_scalar_mul hT hφ ![e a, e i, e j]
    change D.covariantTensorDerivative (fun y v => φ y * T y v) x ![e a, e i, e j] =
      mvfderiv (𝓡 n) φ x (e a) * T x ![e i, e j] +
        φ x * D.covariantTensorDerivative T x ![e a, e i, e j] at hd
    rw [hd]
    ring
  change (∑ a, ∑ i, ∑ j, F x ![e a, e i, e j] *
    D.covariantTensorDerivative (fun y v => φ y * T y v) x ![e a, e i, e j]) = _
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    RiemannianMetric.tensorPairingThree, RiemannianMetric.tensorPairingCovector,
    Matrix.cons_val_zero, e]

theorem tensorPairingThree_derivative_scalar_mul (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {φ : M → ℝ} {x : M} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x) :
    g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative (fun y v => φ y * T y v)) x =
      φ x * g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative T) x +
      (1 / 2 : ℝ) * g.inner x (D.gradient φ x)
        (D.gradient (g.tensorPairingTwo T T) x) := by
  rw [D.tensorPairingThree_derivative_scalar_mul_cross _ hT hφ]
  congr 1
  have hterm (a) :
      mvfderiv (𝓡 n) φ x (g.orthonormalBasis x a) *
          g.tensorPairingCovector (D.covariantTensorDerivative T) T x
            ![g.orthonormalBasis x a] =
        (1 / 2 : ℝ) * (mvfderiv (𝓡 n) φ x (g.orthonormalBasis x a) *
          mvfderiv (𝓡 n) (g.tensorPairingTwo T T) x (g.orthonormalBasis x a)) := by
    have hd := D.mvfderiv_tensorPairingTwo hT hT x (g.orthonormalBasis x a)
    rw [hd]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, D.sum_mvfderiv_mul_eq_inner_gradient]

theorem tensorPairingThree_derivative_regularized_power_cross (D : LeviCivitaData g)
    (F : CovariantTensorEvaluation n M 3)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) (x : M) :
    let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
    g.tensorPairingThree F
        (D.covariantTensorDerivative (fun y v =>
          (η y ^ 2 * w y ^ (2 * p - 2)) * T y v)) x =
      η x ^ 2 * w x ^ (2 * p - 2) *
        g.tensorPairingThree F (D.covariantTensorDerivative T) x +
      2 * η x * w x ^ (2 * p - 2) *
        (∑ a, mvfderiv (𝓡 n) η x (g.orthonormalBasis x a) *
          g.tensorPairingCovector F T x ![g.orthonormalBasis x a]) +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 3) *
        (∑ a, mvfderiv (𝓡 n) w x (g.orthonormalBasis x a) *
          g.tensorPairingCovector F T x ![g.orthonormalBasis x a]) := by
  let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
  let φ := fun y => η y ^ 2 * w y ^ (2 * p - 2)
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := D.contMDiff_regularized_tensor_norm hT hε
  have hwpos (y : M) : 0 < w y := regularized_tensor_norm_pos T hε y
  have hpower := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ := (hη.pow 2).mul hpower
  have hηsq : D.gradient (fun y => η y ^ 2) x =
      η x • D.gradient η x + η x • D.gradient η x := by
    simpa only [pow_two] using D.gradient_mul
      ((hη x).mdifferentiableAt (by simp)) ((hη x).mdifferentiableAt (by simp))
  have hφder (v : TangentSpace (𝓡 n) x) : mvfderiv (𝓡 n) φ x v =
      2 * η x * w x ^ (2 * p - 2) * mvfderiv (𝓡 n) η x v +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 3) * mvfderiv (𝓡 n) w x v := by
    rw [← D.inner_gradient]
    dsimp only [φ]
    rw [D.gradient_mul (((hη.pow 2) x).mdifferentiableAt (by simp))
      ((hpower x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos, hηsq]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, D.inner_gradient,
      show 2 * p - 2 - 1 = 2 * p - 3 by ring]
    ring
  change g.tensorPairingThree F
    (D.covariantTensorDerivative (fun y v => φ y * T y v)) x = _
  rw [D.tensorPairingThree_derivative_scalar_mul_cross F hT
    ((hφ x).mdifferentiableAt (by simp))]
  simp_rw [hφder, add_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, φ, w]
  ring

theorem tensorPairingThree_derivative_regularized_power (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) (x : M) :
    let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
    g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative (fun y v =>
          (η y ^ 2 * w y ^ (2 * p - 2)) * T y v)) x =
      η x ^ 2 * w x ^ (2 * p - 2) *
        g.tensorPairingThree (D.covariantTensorDerivative T)
          (D.covariantTensorDerivative T) x +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 2) *
        g.inner x (D.gradient w x) (D.gradient w x) +
      2 * η x * w x ^ (2 * p - 1) * g.inner x (D.gradient η x) (D.gradient w x) := by
  let Q := g.tensorPairingTwo T T
  let w := fun y => Real.sqrt (Q y + ε)
  let φ := fun y => η y ^ 2 * w y ^ (2 * p - 2)
  have hQ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q := D.contMDiff_tensorPairingTwo hT hT
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := D.contMDiff_regularized_tensor_norm hT hε
  have hwpos (y : M) : 0 < w y := regularized_tensor_norm_pos T hε y
  have hwsq (y : M) : w y ^ 2 = Q y + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos y)).le
  have hshift (y : M) : mvfderiv (𝓡 n) (fun z => Q z + ε) y =
      mvfderiv (𝓡 n) Q y := by
    simpa only [mvfderiv_const, add_zero] using
      mvfderiv_fun_add ((hQ y).mdifferentiableAt (by simp))
        (mdifferentiableAt_const (c := ε))
  have hgshift : D.gradient (fun y => Q y + ε) x = D.gradient Q x := by
    simp only [gradient, hshift]
  have hgrad := D.gradient_mul ((hw x).mdifferentiableAt (by simp))
    ((hw x).mdifferentiableAt (by simp))
  change D.gradient (fun y => w y * w y) x =
    w x • D.gradient w x + w x • D.gradient w x at hgrad
  simp only [← pow_two, hwsq, hgshift] at hgrad
  have hηsq : D.gradient (fun y => η y ^ 2) x =
      η x • D.gradient η x + η x • D.gradient η x := by
    simpa only [pow_two] using D.gradient_mul
      ((hη x).mdifferentiableAt (by simp)) ((hη x).mdifferentiableAt (by simp))
  have hpower := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ := (hη.pow 2).mul hpower
  have hpow1 : w x ^ (2 * p - 2 - 1) * w x = w x ^ (2 * p - 2) := by
    rw [← Real.rpow_add_one (hwpos x).ne', sub_add_cancel]
  have hpow2 : w x ^ (2 * p - 2) * w x = w x ^ (2 * p - 1) := by
    rw [← Real.rpow_add_one (hwpos x).ne']
    congr 1
    ring
  change g.tensorPairingThree (D.covariantTensorDerivative T)
    (D.covariantTensorDerivative (fun y v => φ y * T y v)) x = _
  rw [D.tensorPairingThree_derivative_scalar_mul hT
    ((hφ x).mdifferentiableAt (by simp))]
  change φ x * _ + (1 / 2 : ℝ) * g.inner x (D.gradient φ x) (D.gradient Q x) = _
  calc
    _ = η x ^ 2 * w x ^ (2 * p - 2) *
        g.tensorPairingThree (D.covariantTensorDerivative T)
          (D.covariantTensorDerivative T) x +
        (2 * p - 2) * η x ^ 2 * (w x ^ (2 * p - 2 - 1) * w x) *
          g.inner x (D.gradient w x) (D.gradient w x) +
        2 * η x * (w x ^ (2 * p - 2) * w x) *
          g.inner x (D.gradient η x) (D.gradient w x) := by
      dsimp only [φ]
      rw [D.gradient_mul (((hη.pow 2) x).mdifferentiableAt (by simp))
        ((hpower x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos,
        hηsq, hgrad]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring
    _ = _ := by rw [hpow1, hpow2]

end LeviCivitaData
end PoincareConjecture

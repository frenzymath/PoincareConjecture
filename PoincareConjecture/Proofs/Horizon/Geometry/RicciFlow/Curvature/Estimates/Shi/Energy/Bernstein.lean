import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarChainRule
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def scalarGradientPairing (g : RiemannianMetric n M)
    (f h : M → ℝ) (x : M) : ℝ :=
  ∑ i, mvfderiv (𝓡 n) f x (g.orthonormalBasis x i) *
    mvfderiv (𝓡 n) h x (g.orthonormalBasis x i)

theorem scalarGradientPairing_sq_le (g : RiemannianMetric n M)
    (f h : M → ℝ) (x : M) :
    scalarGradientPairing g f h x ^ 2 ≤
      scalarGradientSq g f x * scalarGradientSq g h x := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

private theorem empty_append_cast {k : ℕ} {V : Type*}
    (v : Fin 0 → V) (w : Fin k → V) :
    (fun i => Fin.append v w (Fin.cast (Nat.zero_add k).symm i)) = w := by
  rw [Fin.append_left_nil v w rfl]
  funext i
  apply congrArg w
  apply Fin.ext
  rfl

private theorem derivative_rank_cast (D : LeviCivitaData g)
    {k l : ℕ} (h : k = l) (T : CovariantTensorEvaluation n M k)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (w : Fin l → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorRankCast h T) x (Fin.cons v w) =
      D.covariantTensorDerivative T x
        (Fin.cons v (fun i => w (Fin.cast h i))) := by
  cases h
  rfl

private theorem derivative_rank_zero (D : LeviCivitaData g) (f : M → ℝ)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (w : Fin 0 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y (_ : Fin 0 → TangentSpace (𝓡 n) y) => f y)
      x (Fin.cons v w) = mvfderiv (𝓡 n) f x v := by
  simp [LeviCivitaData.covariantTensorDerivative]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_tensorNorm_sq (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => (g.tensorNorm T y) ^ 2) x v =
      2 * (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        T x (fun i => g.orthonormalBasis x (a i)) *
          D.covariantTensorDerivative T x
            (Fin.cons v (fun i => g.orthonormalBasis x (a i)))) := by
  classical
  let A : CovariantTensorEvaluation n M (0 + r * 2) :=
    tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct T T)
  have hcast {k l : ℕ} (h : k = l) {S : CovariantTensorEvaluation n M k}
      (hS : IsSmoothCovariantTensor S) : IsSmoothCovariantTensor (tensorRankCast h S) := by
    cases h
    exact hS
  have hA : IsSmoothCovariantTensor A :=
    hcast _ (isSmoothCovariantTensor_pairedProduct hT hT)
  have htrace : tensorPairTrace (p := 0) (r := r) g A =
      (fun y (_ : Fin 0 → TangentSpace (𝓡 n) y) => (g.tensorNorm T y) ^ 2) := by
    funext y w
    unfold RiemannianMetric.tensorNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    change (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)),
      pairedProduct T T y
      (fun j => Fin.append w
        (pairedDiagonal (fun i => g.orthonormalBasis y (a i)))
        (Fin.cast (Nat.zero_add (r * 2)).symm j))) = _
    apply Finset.sum_congr rfl
    intro a _
    rw [empty_append_cast]
    simp only [pairedProduct, pairedDiagonal, Equiv.symm_apply_apply, pow_two]
  have hd := covariantTensorDerivative_tensorPairTrace D hA x v
    (fun i : Fin 0 => Fin.elim0 i)
  rw [htrace, derivative_rank_zero] at hd
  rw [hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [A]
  rw [derivative_rank_cast, empty_append_cast,
    covariantTensorDerivative_pairedProduct D hT hT]
  simp only [pairedDiagonal, Equiv.symm_apply_apply]
  ring

private theorem tensorNorm_sq_cons (g : RiemannianMetric n M) {r : ℕ}
    (S : CovariantTensorEvaluation n M (r + 1)) (x : M) :
    (g.tensorNorm S x) ^ 2 =
      ∑ i, ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (S x (Fin.cons (g.orthonormalBasis x i)
          (fun j => g.orthonormalBasis x (a j)))) ^ 2 := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let q (a : Fin (r + 1) → Fin d) := (S x (fun j => b (a j))) ^ 2
  change (Real.sqrt (∑ a, q a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin d)).sum_comp q,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (S x (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j))) ^ 2 = _
  have he : (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j)) =
      (Fin.cons (b i) (fun j => b (a j)) : Fin (r + 1) → TangentSpace (𝓡 n) x) :=
    Fin.comp_cons b i a
  rw [he]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem scalarGradientSq_tensorNorm_sq_le (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T) (x : M) :
    scalarGradientSq g (fun y => (g.tensorNorm T y) ^ 2) x ≤
      4 * (g.tensorNorm T x) ^ 2 *
        (g.tensorNorm (D.covariantTensorDerivative T) x) ^ 2 := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let f (a : Fin r → Fin d) := T x (fun j => b (a j))
  let q (i : Fin d) (a : Fin r → Fin d) :=
    D.covariantTensorDerivative T x (Fin.cons (b i) (fun j => b (a j)))
  have hnorm : (g.tensorNorm T x) ^ 2 = ∑ a, f a ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnext : (g.tensorNorm (D.covariantTensorDerivative T) x) ^ 2 =
      ∑ i, ∑ a, q i a ^ 2 := tensorNorm_sq_cons g _ x
  unfold scalarGradientSq
  simp_rw [mvfderiv_tensorNorm_sq D hT]
  change (∑ i : Fin d, (2 * ∑ a, f a * q i a) ^ 2) ≤ _
  rw [hnorm, hnext, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (q i)
  nlinarith only [h]

private theorem smooth_iterated_curvature (D : LeviCivitaData g) (m : ℕ) :
    IsSmoothCovariantTensor
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) := by
  induction m with
  | zero => exact isSmoothCovariantTensor_riemannEvaluation D
  | succ m ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih

theorem scalarGradientSq_curvatureDerivativeEnergy_le
    (D : LeviCivitaData g) (m : ℕ) (x : M) :
    scalarGradientSq g (fun y => (D.curvatureDerivativeNorm m y) ^ 2) x ≤
      4 * (D.curvatureDerivativeNorm m x) ^ 2 *
        (D.curvatureDerivativeNorm (m + 1) x) ^ 2 := by
  exact scalarGradientSq_tensorNorm_sq_le D (smooth_iterated_curvature D m) x

theorem curvatureDerivativeEnergy_gradient_cross_le
    (D : LeviCivitaData g) (m : ℕ) (x : M) :
    -2 * scalarGradientPairing g
      (fun y => (D.curvatureDerivativeNorm m y) ^ 2)
      (fun y => (D.curvatureDerivativeNorm (m + 1) y) ^ 2) x ≤
      ((D.curvatureDerivativeNorm (m + 1) x) ^ 2) ^ 2 +
        16 * (D.curvatureDerivativeNorm m x) ^ 2 *
          (D.curvatureDerivativeNorm (m + 2) x) ^ 2 := by
  let f := fun y => (D.curvatureDerivativeNorm m y) ^ 2
  let h := fun y => (D.curvatureDerivativeNorm (m + 1) y) ^ 2
  let u := f x
  let v := h x
  let w := (D.curvatureDerivativeNorm (m + 2) x) ^ 2
  let p := scalarGradientPairing g f h x
  have hu : 0 ≤ u := sq_nonneg _
  have hv : 0 ≤ v := sq_nonneg _
  have hw : 0 ≤ w := sq_nonneg _
  have hcs : p ^ 2 ≤ scalarGradientSq g f x * scalarGradientSq g h x :=
    scalarGradientPairing_sq_le g f h x
  have hf := scalarGradientSq_curvatureDerivativeEnergy_le D m x
  have hh := scalarGradientSq_curvatureDerivativeEnergy_le D (m + 1) x
  have hproduct : scalarGradientSq g f x * scalarGradientSq g h x ≤
      (4 * u * v) * (4 * v * w) :=
    mul_le_mul hf hh (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  have hbound : p ^ 2 ≤ 16 * u * v ^ 2 * w := by
    nlinarith only [hcs.trans hproduct]
  have hrhs : 0 ≤ v ^ 2 + 16 * u * w := by positivity
  change -2 * p ≤ v ^ 2 + 16 * u * w
  nlinarith [sq_nonneg (v ^ 2 - 16 * u * w),
    sq_nonneg (v ^ 2 + 16 * u * w + 2 * p)]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_const_add_mul (D : LeviCivitaData g) (A : ℝ)
    {f h : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    D.laplacian (fun y => (A + f y) * h y) x =
      (A + f x) * D.laplacian h x + h x * D.laplacian f x +
        2 * scalarGradientPairing g f h x := by
  have hfd (y : M) := (hf y).mdifferentiableAt (by simp)
  have hhd (y : M) := (hh y).mdifferentiableAt (by simp)
  have hafd (y : M) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun z => A + f z) y :=
    mdifferentiableAt_const.add (hfd y)
  have hprod (y : M) (v : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) (fun z => (A + f z) * h z) y v =
        (A + f y) * mvfderiv (𝓡 n) h y v +
          h y * mvfderiv (𝓡 n) f y v := by
    simp only [mvfderiv_fun_mul (hafd y) (hhd y),
      mvfderiv_fun_add mdifferentiableAt_const (hfd y), mvfderiv_const,
      zero_add, add_apply, smul_apply, smul_eq_mul]
  have hH (u v : TangentSpace (𝓡 n) x) :
      D.hessian (fun y => (A + f y) * h y) x u v =
        (A + f x) * D.hessian h x u v + h x * D.hessian f x u v +
          mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) h x v +
          mvfderiv (𝓡 n) h x u * mvfderiv (𝓡 n) f x v := by
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    let df := fun y => mvfderiv (𝓡 n) f y (Y y)
    let dh := fun y => mvfderiv (𝓡 n) h y (Y y)
    have hdf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) df x :=
      (contMDiffAt_directional_derivative (hf x)
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) v)).mdifferentiableAt (by simp)
    have hdh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dh x :=
      (contMDiffAt_directional_derivative (hh x)
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) v)).mdifferentiableAt (by simp)
    have he : (fun y => mvfderiv (𝓡 n) (fun z => (A + f z) * h z) y (Y y)) =
        (fun y => (A + f y) * dh y + h y * df y) := funext fun y => hprod y (Y y)
    have hd : mvfderiv (𝓡 n)
        (fun y => mvfderiv (𝓡 n) (fun z => (A + f z) * h z) y (Y y)) x u =
        (A + f x) * mvfderiv (𝓡 n) dh x u +
          mvfderiv (𝓡 n) h x v * mvfderiv (𝓡 n) f x u +
          (h x * mvfderiv (𝓡 n) df x u +
            mvfderiv (𝓡 n) f x v * mvfderiv (𝓡 n) h x u) := by
      rw [he]
      erw [mvfderiv_fun_add ((hafd x).mul hdh) ((hhd x).mul hdf),
        mvfderiv_fun_mul (hafd x) hdh, mvfderiv_fun_mul (hhd x) hdf,
        mvfderiv_fun_add mdifferentiableAt_const (hfd x), mvfderiv_const]
      simp only [zero_add, add_apply, smul_apply, smul_eq_mul,
        df, dh, Y, FiberBundle.extend_apply_self]
    change mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n) (fun z => (A + f z) * h z) y (Y y)) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x) -
      mvfderiv (𝓡 n) (fun z => (A + f z) * h z) x
        (D.connection Y x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x)) = _
    simp only [FiberBundle.extend_apply_self]
    rw [hd, hprod]
    simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
      FiberBundle.extend_apply_self]
    change _ = (A + f x) *
      (mvfderiv (𝓡 n) dh x u - mvfderiv (𝓡 n) h x (D.connection Y x u)) +
      h x * (mvfderiv (𝓡 n) df x u - mvfderiv (𝓡 n) f x (D.connection Y x u)) + _ + _
    ring
  simp only [LeviCivitaData.laplacian, hH, Finset.sum_add_distrib,
    ← Finset.mul_sum, scalarGradientPairing]
  have hcomm : (∑ i, mvfderiv (𝓡 n) h x (g.orthonormalBasis x i) *
      mvfderiv (𝓡 n) f x (g.orthonormalBasis x i)) = scalarGradientPairing g f h x := by
    unfold scalarGradientPairing
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hcomm]
  unfold scalarGradientPairing
  ring

end PoincareConjecture.RicciFlowAnalysis

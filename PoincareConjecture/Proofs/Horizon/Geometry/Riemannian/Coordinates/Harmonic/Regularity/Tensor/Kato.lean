import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Pairing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorNorm

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_tensor_normSq_le (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) (x : M) :
    let Q := g.tensorPairingTwo T T
    g.inner x (D.gradient Q x) (D.gradient Q x) ≤
      4 * Q x * g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative T) x := by
  let Q := g.tensorPairingTwo T T
  let e := g.orthonormalBasis x
  have hderiv (k) : mvfderiv (𝓡 n) Q x (e k) =
      2 * ∑ i, ∑ j, D.covariantTensorDerivative T x ![e k, e i, e j] * T x ![e i, e j] := by
    have h := D.mvfderiv_tensorPairingTwo hT hT x (e k)
    simpa only [Q, RiemannianMetric.tensorPairingCovector, Matrix.cons_val_zero,
      ← two_mul] using h
  dsimp only
  rw [D.gradient_normSq_eq_sum_mvfderiv_sq]
  change (∑ k, (mvfderiv (𝓡 n) Q x (e k)) ^ 2) ≤ _
  simp only [RiemannianMetric.tensorPairingThree]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [hderiv]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        D.covariantTensorDerivative T x ![e k, e p.1, e p.2])
    (fun p => T x ![e p.1, e p.2])
  simp only [Fintype.sum_prod_type] at hcs
  change (2 * ∑ i, ∑ j, D.covariantTensorDerivative T x ![e k, e i, e j] *
    T x ![e i, e j]) ^ 2 ≤
      4 * (∑ i, ∑ j, T x ![e i, e j] * T x ![e i, e j]) *
        (∑ i, ∑ j, D.covariantTensorDerivative T x ![e k, e i, e j] *
          D.covariantTensorDerivative T x ![e k, e i, e j])
  simp only [← pow_two]
  nlinarith only [hcs]

theorem regularized_tensor_norm_pos (T : CovariantTensorEvaluation n M 2)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    0 < Real.sqrt (g.tensorPairingTwo T T x + ε) :=
  Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (g.tensorPairingTwo_self_nonneg T x) hε)

theorem contMDiff_regularized_tensor_norm (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => Real.sqrt (g.tensorPairingTwo T T x + ε)) := by
  intro x
  have hpos := Real.sqrt_pos.mp (regularized_tensor_norm_pos (g := g) T hε x)
  exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp x
    ((D.contMDiff_tensorPairingTwo hT hT x).add contMDiffAt_const)

theorem gradient_regularized_tensor_norm_le (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
    g.inner x (D.gradient w x) (D.gradient w x) ≤
      g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative T) x := by
  let Q := g.tensorPairingTwo T T
  let w := fun y => Real.sqrt (Q y + ε)
  let A := g.tensorPairingThree (D.covariantTensorDerivative T)
    (D.covariantTensorDerivative T) x
  have hA : 0 ≤ A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hwpos (y : M) : 0 < w y := regularized_tensor_norm_pos (g := g) T hε y
  have hwsq (y : M) : w y ^ 2 = Q y + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos y)).le
  have hQ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q := D.contMDiff_tensorPairingTwo hT hT
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := D.contMDiff_regularized_tensor_norm hT hε
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
  have hgradSq : g.inner x (D.gradient Q x) (D.gradient Q x) =
      4 * w x ^ 2 * g.inner x (D.gradient w x) (D.gradient w x) := by
    rw [hgrad]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hKato := D.gradient_tensor_normSq_le hT x
  change g.inner x (D.gradient Q x) (D.gradient Q x) ≤ 4 * Q x * A at hKato
  rw [hgradSq] at hKato
  change g.inner x (D.gradient w x) (D.gradient w x) ≤ A
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * w x ^ 2 from
    mul_pos (by norm_num) (sq_pos_of_pos (hwpos x)))).mp
  nlinarith only [hKato, congrArg (fun z => 4 * z * A) (hwsq x), mul_nonneg hε.le hA]

end PoincareConjecture.LeviCivitaData

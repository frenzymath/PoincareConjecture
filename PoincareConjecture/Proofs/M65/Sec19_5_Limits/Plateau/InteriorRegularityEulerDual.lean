import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerMetric
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussConnectionCoefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Euler

variable {N : ℕ}




def metricDualField (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (k : Fin N) (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (g.euclideanCoefficients x).inverse (EuclideanSpace.proj k)



theorem contDiff_metricDualField (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (k : Fin N) : ContDiff ℝ ∞ (metricDualField g k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hi : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  exact (hi.contDiffAt_map_inverse.comp x (g.contDiffAt_euclideanCoefficients x)).clm_apply
    contDiffAt_const




theorem metricDualField_pairing (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (k : Fin N) (x a : EuclideanSpace ℝ (Fin N)) :
    g.inner x (metricDualField g k x) a = a k := by
  exact congrArg (fun L => L a)
    ((g.inner_isInvertible x).self_apply_inverse (EuclideanSpace.proj k))

private theorem metricDualField_derivative_pairing
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (k : Fin N) (x a u : EuclideanSpace ℝ (Fin N)) :
    fderiv ℝ g.euclideanCoefficients x u (metricDualField g k x) a +
      g.inner x (fderiv ℝ (metricDualField g k) x u) a = 0 := by
  have hG := (g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)
  have hV := (contDiff_metricDualField g k).differentiable (by simp) x
  have hd := ((hG.hasFDerivAt.clm_apply hV.hasFDerivAt).clm_apply (hasFDerivAt_const a x)).fderiv
  have heq : (fun y => g.euclideanCoefficients y (metricDualField g k y) a) = fun _ => a k := by
    funext y
    exact metricDualField_pairing g k y a
  rw [heq, fderiv_const_apply] at hd
  have h := congrArg (fun L => L u) hd
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    add_apply, ContinuousLinearMap.comp_apply, zero_apply] at h
  change 0 = g.inner x (fderiv ℝ (metricDualField g k) x u) a +
    fderiv ℝ g.euclideanCoefficients x u (metricDualField g k x) a at h
  linarith only [h]





theorem metricDual_firstVariation
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    (k : Fin N) (x a : EuclideanSpace ℝ (Fin N)) (α β : ℝ) :
    (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients x (α • metricDualField g k x) a a +
      g.inner x (α • fderiv ℝ (metricDualField g k) x a + β • metricDualField g k x) a =
        β * a k - α * (M65Gauss.connectionCoefficient D x a a) k := by
  have hder := metricDualField_derivative_pairing g k x a a
  have hcompat := M65Gauss.connectionCoefficient_metricCompatible D x a (metricDualField g k x) a
  have hswap := M65Gauss.connectionCoefficient_metricCompatible D x (metricDualField g k x) a a
  rw [metricDualField_pairing] at hcompat
  rw [g.symm x a, M65Gauss.connectionCoefficient_symm D x (metricDualField g k x) a] at hswap
  have hbase : g.inner x (fderiv ℝ (metricDualField g k) x a) a +
      (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients x (metricDualField g k x) a a =
        -(M65Gauss.connectionCoefficient D x a a) k := by
    linarith only [hder, hcompat, hswap]
  simp only [map_smul, smul_apply, map_add, add_apply, smul_eq_mul, metricDualField_pairing]
  linear_combination α * hbase

end PoincareConjecture.M65Euler

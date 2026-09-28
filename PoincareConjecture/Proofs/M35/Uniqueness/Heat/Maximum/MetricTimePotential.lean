import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricPotential
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.IntegralEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def metricEntropyTimePotential {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : V → ℝ) (Q : ℝ) (p : V × V) : ℝ :=
  (η p.1 * g.pullbackVolumeDensity id p.1) *
    (-(D.scalarCurvature p.1) * normBoundEntropy Q (g.inner p.1 p.2 p.2) -
      2 * Real.smoothTransition (g.inner p.1 p.2 p.2 - Q) * D.ricci p.1 p.2 p.2)

theorem metricEntropyTimePotential_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (Q : ℝ) :
    ContDiff ℝ ∞ (metricEntropyTimePotential D η Q) := by
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hRic : ContDiff ℝ ∞ (fun p : V × V => D.ricci p.1 p.2 p.2) := by
    have h := (((hg.comp contDiff_fst).clm_apply
      (((rawRicciLinear_contDiff D).comp contDiff_fst).clm_apply contDiff_snd)).clm_apply
        contDiff_snd)
    convert! h using 1
    funext p
    exact (inner_ricciSharp D p.1 p.2 p.2).symm
  exact ((hη.mul (raw_volumeDensity_contDiff g)).comp contDiff_fst).mul
    (((raw_scalar_contDiff D).comp contDiff_fst).neg.mul
      ((normBoundEntropy_contDiff Q).comp (metric_quadratic_contDiff g)) |>.sub
        ((contDiff_const.mul (Real.smoothTransition.contDiff.comp
          ((metric_quadratic_contDiff g).sub contDiff_const))).mul hRic))

theorem metricEntropyPotential_hasDerivWithinAt {J : Set ℝ} (F : RicciFlow n V J)
    (η : V → ℝ) (Q : ℝ) {t : ℝ} (ht : t ∈ J) (x z : V) :
    HasDerivWithinAt (fun s => metricEntropyPotential (F.metric s) η Q (x, z))
      (metricEntropyTimePotential (F.connection t) η Q (x, z)) J t := by
  have hq := F.equation t ht x z z
  have he := (normBoundEntropy_hasDerivAt Q ((F.metric t).inner x z z)).comp_hasDerivWithinAt t hq
  have hρ := (raw_volumeDensity_hasDerivWithinAt F ht x).const_mul (η x)
  have h := hρ.mul he
  convert! h using 1
  simp only [metricEntropyTimePotential, Function.comp_def]
  ring

theorem metricEntropy_test_pair (g : RiemannianMetric n V) (η : V → ℝ) (Q : ℝ) (x z w : V) :
    (∑ j, metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, z) * w j) =
      2 * η x * g.pullbackVolumeDensity id x *
        Real.smoothTransition (g.inner x z z - Q) * g.inner x z w := by
  have hw := congrArg (g.euclideanCoefficients x z)
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w)
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] at hw
  simp only [metricEntropyTest, metricEntropyLinear, smul_apply, smul_eq_mul]
  change _ = 2 * η x * g.pullbackVolumeDensity id x *
    Real.smoothTransition (g.inner x z z - Q) * g.euclideanCoefficients x z w
  rw [← hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : g.euclideanCoefficients x (EuclideanSpace.single j 1) z =
      g.euclideanCoefficients x z (EuclideanSpace.single j 1) :=
    g.symm x (EuclideanSpace.single j 1) z
  rw [hs]
  ring

theorem metricEntropy_operator_cancellation {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : V → ℝ) (Q : ℝ) (X : V → V) (x : V) :
    (∑ j, metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, X x) *
      (@Add.add V inferInstance (fieldTraceHessian D X x)
        (RicciFlow.ricciSharp D x (X x))) j) +
        metricEntropyTimePotential D η Q (x, X x) =
      η x * g.pullbackVolumeDensity id x * fieldEntropySource D X (normBoundEntropy Q) x := by
  rw [metricEntropy_test_pair]
  have hpair : g.inner x (X x) (@Add.add V inferInstance (fieldTraceHessian D X x)
      (RicciFlow.ricciSharp D x (X x))) =
      g.inner x (fieldTraceHessian D X x) (X x) + D.ricci x (X x) (X x) := by
    change g.euclideanCoefficients x (X x)
      (fieldTraceHessian D X x + rawRicciLinear D x (X x)) = _
    rw [map_add]
    have h₁ : g.euclideanCoefficients x (X x) (fieldTraceHessian D X x) =
        g.inner x (fieldTraceHessian D X x) (X x) := g.symm x _ _
    have h₂ : g.euclideanCoefficients x (X x) (rawRicciLinear D x (X x)) =
        D.ricci x (X x) (X x) :=
      (g.symm x _ _).trans (inner_ricciSharp D x (X x) (X x))
    rw [h₁, h₂]
  rw [hpair]
  simp only [metricEntropyTimePotential, fieldEntropySource,
    normBoundEntropy_deriv, fieldNormSq]
  ring

end PoincareConjecture.M35.Uniqueness.Heat

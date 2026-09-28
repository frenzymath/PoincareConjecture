import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Holder

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

noncomputable def principalOperator (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (g.euclideanCoefficients x).inverse.comp (innerSL ℝ)

lemma contDiff_principalOperator : ContDiff ℝ ∞ g.principalOperator := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hI := (g.inner_isInvertible x).contDiffAt_map_inverse.comp x
    (g.contDiffAt_euclideanCoefficients x)
  exact hI.clm_comp contDiffAt_const

lemma principalOperator_symmetric (x v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (g.principalOperator x v) w = inner ℝ v (g.principalOperator x w) := by
  have h := g.symm x (g.principalOperator x v) (g.principalOperator x w)
  change (g.inner x) ((g.inner x).inverse (innerSL ℝ v))
      ((g.inner x).inverse (innerSL ℝ w)) =
    (g.inner x) ((g.inner x).inverse (innerSL ℝ w))
      ((g.inner x).inverse (innerSL ℝ v)) at h
  rw [(g.inner_isInvertible x).self_apply_inverse,
    (g.inner_isInvertible x).self_apply_inverse] at h
  change inner ℝ v (g.principalOperator x w) =
    inner ℝ w (g.principalOperator x v) at h
  rw [real_inner_comm]
  exact h.symm

lemma principalOperator_elliptic (x : EuclideanSpace ℝ (Fin n))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    (1 / b) * ‖v‖ ^ 2 ≤ inner ℝ v (g.principalOperator x v) ∧
      inner ℝ v (g.principalOperator x v) ≤ (1 / a) * ‖v‖ ^ 2 := by
  constructor
  · simpa only [one_div_mul_eq_div, principalOperator, ContinuousLinearMap.comp_apply,
      euclideanCoefficients] using
      CoordinateExponential.le_inner_inverse_innerSL ha hb (g.symm x) hlower hupper v
  · simpa only [one_div_mul_eq_div, principalOperator, ContinuousLinearMap.comp_apply,
      euclideanCoefficients] using
      CoordinateExponential.inner_inverse_innerSL_le ha hlower v

lemma norm_principalOperator_sub_le (x y : EuclideanSpace ℝ (Fin n))
    {a : ℝ} (ha : 0 < a)
    (hx : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hy : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner y v v) :
    ‖g.principalOperator x - g.principalOperator y‖ ≤
      ‖g.euclideanCoefficients x - g.euclideanCoefficients y‖ / a ^ 2 := by
  have h := CoordinateExponential.norm_inverse_sub_le_of_ellipticity ha hx hy
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv := ((g.euclideanCoefficients x).inverse -
    (g.euclideanCoefficients y).inverse).le_opNorm (innerSL ℝ v)
  rw [innerSL_apply_norm] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right h (norm_nonneg v))

lemma norm_principalOperator_sub_le_rpow {a R H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hell : ∀ z ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.inner z v v)
    (hderiv : ∀ z ∈ Metric.ball 0 R, ‖fderiv ℝ g.euclideanCoefficients z‖ ≤ H)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R)
    (hy : y ∈ Metric.ball 0 R) :
    ‖g.principalOperator x - g.principalOperator y‖ ≤
      ((H * Real.sqrt (2 * R)) / a ^ 2) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ ‖g.euclideanCoefficients x - g.euclideanCoefficients y‖ / a ^ 2 :=
      g.norm_principalOperator_sub_le x y ha (hell x hx) (hell y hy)
    _ ≤ ((H * Real.sqrt (2 * R)) * Real.sqrt ‖x - y‖) / a ^ 2 :=
      div_le_div_of_nonneg_right (g.norm_coefficients_sub_le_sqrt hH hderiv hx hy)
        (sq_nonneg _)
    _ = _ := by simp only [Real.sqrt_eq_rpow]; ring

lemma inner_basis_principalOperator_basis (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (g.principalOperator x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        g.inverseCoefficients x i j := by
  have hproj : innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j) =
      EuclideanSpace.proj j := by
    ext v
    simp only [innerSL_apply_apply, EuclideanSpace.basisFun_inner, PiLp.proj_apply]
  rw [principalOperator, ContinuousLinearMap.comp_apply, hproj,
    EuclideanSpace.basisFun_inner, g.inverseCoefficients_symm x i j]
  rfl

end PoincareConjecture.RiemannianMetric

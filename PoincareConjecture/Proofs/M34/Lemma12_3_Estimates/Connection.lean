import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.RadialForm
import PoincareConjecture.Proofs.M34.Mathlib.WeightedRadialConnection
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34



noncomputable def initialRankOneCoefficient (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (initialRadialCoefficient g₀ r - initialAngularCoefficient g₀ r) / r ^ 2



theorem initialRankOneCoefficient_contDiffAt (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ ∞ (initialRankOneCoefficient g₀) r :=
  ((initialRadialCoefficient_contDiff g₀).contDiffAt.sub
    (initialAngularCoefficient_contDiff g₀).contDiffAt).div
      (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)


noncomputable def initialChristoffelA (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (initialAngularCoefficient g₀) r / (2 * r * initialAngularCoefficient g₀ r)



noncomputable def initialChristoffelB (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (initialRankOneCoefficient g₀ r - deriv (initialAngularCoefficient g₀) r / (2 * r)) /
    initialRadialCoefficient g₀ r


noncomputable def initialChristoffelC (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  (deriv (initialRankOneCoefficient g₀) r / (2 * r) -
    2 * initialChristoffelA g₀ r * initialRankOneCoefficient g₀ r) /
      initialRadialCoefficient g₀ r



theorem initialChristoffel_contDiffAt (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (initialChristoffelA g₀) r ∧
      ContDiffAt ℝ ∞ (initialChristoffelB g₀) r ∧
        ContDiffAt ℝ ∞ (initialChristoffelC g₀) r := by
  have hl := (initialRadialCoefficient_contDiff g₀).contDiffAt (x := r)
  have hc := (initialAngularCoefficient_contDiff g₀).contDiffAt (x := r)
  have hb := initialRankOneCoefficient_contDiffAt g₀ hr
  have hcp : ContDiffAt ℝ ∞ (deriv (initialAngularCoefficient g₀)) r :=
    hc.derivWithin (by simp)
  have hbp : ContDiffAt ℝ ∞ (deriv (initialRankOneCoefficient g₀)) r :=
    hb.derivWithin (by simp)
  have hA : ContDiffAt ℝ ∞ (initialChristoffelA g₀) r := by
    exact hcp.div ((contDiffAt_const.mul contDiffAt_id).mul hc)
      (mul_ne_zero (mul_ne_zero (by norm_num) hr) (initialCoefficients_pos g₀ r).2.ne')
  refine ⟨hA, ?_, ?_⟩
  · exact (hb.sub (hcp.div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) hr))).div hl (initialCoefficients_pos g₀ r).1.ne'
  · exact ((hbp.div (contDiffAt_const.mul contDiffAt_id)
      (mul_ne_zero (by norm_num) hr)).sub ((contDiffAt_const.mul hA).mul hb)).div
        hl (initialCoefficients_pos g₀ r).1.ne'



theorem initialMetricInner_fderiv (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    fderiv ℝ (fun y => g₀.metric.inner y u v) x w =
      deriv (initialAngularCoefficient g₀) ‖x‖ / ‖x‖ * inner ℝ x w * inner ℝ u v +
      deriv (initialRankOneCoefficient g₀) ‖x‖ / ‖x‖ * inner ℝ x w *
        (inner ℝ x u * inner ℝ x v) +
      initialRankOneCoefficient g₀ ‖x‖ *
        (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v) := by
  have he : (fun y : StandardCapSpace => g₀.metric.inner y u v) =ᶠ[𝓝 x]
      (fun y => initialAngularCoefficient g₀ ‖y‖ * inner ℝ u v +
        initialRankOneCoefficient g₀ ‖y‖ * (inner ℝ y u * inner ℝ y v)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [initialMetric_radial_inner g₀ hy]
    simp only [initialRankOneCoefficient, mul_assoc]
  rw [he.fderiv_eq]
  exact Poincare.fderiv_radial_pairing hx
    (((initialAngularCoefficient_contDiff g₀).differentiable (by simp)) ‖x‖).hasDerivAt
    ((initialRankOneCoefficient_contDiffAt g₀ (norm_ne_zero_iff.mpr hx)).differentiableAt
      (by simp)).hasDerivAt u v w

set_option backward.isDefEq.respectTransparency false in


theorem initialConnection_formula (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    g₀.connection.connection (fun _ => v) x u =
      Poincare.radialChristoffel (initialChristoffelA g₀ ‖x‖)
        (initialChristoffelB g₀ ‖x‖) (initialChristoffelC g₀ ‖x‖) x u v := by
  apply (g₀.metric.inner_isInvertible x).injective
  ext w
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hl : initialRadialCoefficient g₀ ‖x‖ ≠ 0 := (initialCoefficients_pos g₀ ‖x‖).1.ne'
  have hc : initialAngularCoefficient g₀ ‖x‖ ≠ 0 := (initialCoefficients_pos g₀ ‖x‖).2.ne'
  have hr : initialAngularCoefficient g₀ ‖x‖ +
      initialRankOneCoefficient g₀ ‖x‖ * ‖x‖ ^ 2 = initialRadialCoefficient g₀ ‖x‖ := by
    unfold initialRankOneCoefficient
    field_simp
    ring
  have hA : 2 * initialAngularCoefficient g₀ ‖x‖ * initialChristoffelA g₀ ‖x‖ =
      deriv (initialAngularCoefficient g₀) ‖x‖ / ‖x‖ := by
    unfold initialChristoffelA
    field_simp
  have hB : 2 * initialRadialCoefficient g₀ ‖x‖ * initialChristoffelB g₀ ‖x‖ =
      2 * initialRankOneCoefficient g₀ ‖x‖ -
        deriv (initialAngularCoefficient g₀) ‖x‖ / ‖x‖ := by
    unfold initialChristoffelB
    field_simp
  have hC : 2 * (initialRadialCoefficient g₀ ‖x‖ * initialChristoffelC g₀ ‖x‖ +
      2 * initialChristoffelA g₀ ‖x‖ * initialRankOneCoefficient g₀ ‖x‖) =
      deriv (initialRankOneCoefficient g₀) ‖x‖ / ‖x‖ := by
    unfold initialChristoffelC
    field_simp
    ring
  have hk := g₀.connection.inner_connection_const x u v w
  rw [initialMetricInner_fderiv g₀ hx, initialMetricInner_fderiv g₀ hx,
    initialMetricInner_fderiv g₀ hx] at hk
  have he := Poincare.weightedRadialChristoffel_koszul _ _ _ _ _ _ _ _ x u v w hr hA hB hC
  change g₀.metric.inner x (g₀.connection.connection (fun _ => v) x u) w =
    g₀.metric.inner x _ w
  rw [initialMetric_radial_inner g₀ hx] at hk ⊢
  rw [initialMetric_radial_inner g₀ hx]
  change 2 * (initialAngularCoefficient g₀ ‖x‖ * _ +
    initialRankOneCoefficient g₀ ‖x‖ * _ * _) = _ at hk
  dsimp only [initialRankOneCoefficient] at he hk
  linarith only [hk, he]

end PoincareConjecture.M34

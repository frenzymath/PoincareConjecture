import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.SectionalFormula
import PoincareConjecture.Proofs.M34.Standard.EuclideanCurvature
import Mathlib.Topology.Algebra.Module.PerfectSpace










set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34



theorem capSlope_deriv_round {a r : ℝ} (ha : 0 ≤ a) (hr : r < a) :
    deriv (capSlope a) r = -capProfile a r / 4 := by
  have he : capSlope a =ᶠ[𝓝 r] (fun s => Real.cos (s / 2)) := by
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact capSlope_eq_cos hs.le
  have h := (((hasDerivAt_id' r).div_const 2).cos).congr_of_eventuallyEq he
  rw [h.deriv, capProfile_eq_round ha hr.le]
  ring



theorem capSlope_sq_round {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    capSlope a r ^ 2 = 1 - capProfile a r ^ 2 / 4 := by
  rw [capSlope_eq_cos hr, capProfile_eq_round ha hr]
  nlinarith only [Real.sin_sq_add_cos_sq (r / 2)]

set_option backward.isDefEq.respectTransparency false in



theorem capCurvatureTensor_round {a : ℝ} (ha : 0 < a) (hapi : a ≤ Real.pi / 2)
    (D : LeviCivitaData (capRiemannianMetric a ha hapi))
    {x : StandardCapSpace} (hx : ‖x‖ < a) (u v : StandardCapSpace) :
    D.curvatureTensor x u v u v = (1 / 4 : ℝ) *
      (capMetricInner a x u u * capMetricInner a x v v - capMetricInner a x u v ^ 2) := by
  have hoff {y : StandardCapSpace} (hy : y ≠ 0) (hyr : ‖y‖ < a) :
      D.curvatureTensor y u v u v = (1 / 4 : ℝ) *
        (capMetricInner a y u u * capMetricInner a y v v - capMetricInner a y u v ^ 2) :=
    capCurvatureTensor_eq_quarter_of_profile ha hapi D hy
      (capSlope_deriv_round ha.le hyr) (capSlope_sq_round ha.le hyr.le) u v
  by_cases hx0 : x = 0
  · subst x
    let : PerfectSpace StandardCapSpace := perfectSpace_of_module ℝ StandardCapSpace
    have hi (p q : StandardCapSpace) : Continuous (fun y => capMetricInner a y p q) :=
      ((capMetricInner_contDiff ha).continuous.clm_apply continuous_const).clm_apply
        continuous_const
    have hg : Continuous (fun y => (1 / 4 : ℝ) *
        (capMetricInner a y u u * capMetricInner a y v v - capMetricInner a y u v ^ 2)) :=
      continuous_const.mul (((hi u u).mul (hi v v)).sub ((hi u v).pow 2))
    have he : (fun y => D.curvatureTensor y u v u v) =ᶠ[𝓝[≠] (0 : StandardCapSpace)]
        (fun y => (1 / 4 : ℝ) *
          (capMetricInner a y u u * capMetricInner a y v v - capMetricInner a y u v ^ 2)) := by
      have hb : Metric.ball (0 : StandardCapSpace) a ∈ 𝓝[≠] (0 : StandardCapSpace) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : StandardCapSpace) ha)
      filter_upwards [hb, self_mem_nhdsWithin] with y hy hy0
      apply hoff
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
      · simpa only [dist_zero_right] using Metric.mem_ball.mp hy
    exact tendsto_nhds_unique_of_eventuallyEq
      ((continuous_euclideanCurvatureTensor D u v u v).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) he
  · exact hoff hx0 hx

end PoincareConjecture.M34

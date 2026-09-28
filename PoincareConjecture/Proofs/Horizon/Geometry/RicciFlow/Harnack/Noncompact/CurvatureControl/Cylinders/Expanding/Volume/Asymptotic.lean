import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] uliftChartedSpace uliftIsManifold

theorem ulift_asymptoticVolumeRatio_pos_of_ball_volume_lower_bound
    {n : ℕ} {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (hn : 1 ≤ n)
    (F : RicciFlow n M J) (t : ℝ) (p : M)
    (hcomplete : MetricComplete (F.metric t))
    (hoperator : ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ r : ℝ, 0 < r → ENNReal.ofReal (ν * r ^ n) ≤
      (F.metric t).volumeMeasure ((F.metric t).ball p r)) :
    0 < ((F.ulift : RicciFlow n (ULift.{u} M) J).metric t).asymptoticVolumeRatio
      (ULift.up p) := by
  let : SecondCountableTopology (ULift.{u} M) :=
    (Homeomorph.ulift : ULift.{u} M ≃ₜ M).isEmbedding.secondCountableTopology
  let F' : RicciFlow n (ULift.{u} M) J := F.ulift
  have hc : MetricComplete (F'.metric t) := (F.ulift_metricComplete_iff t).mpr hcomplete
  have hop (x : ULift.{u} M) : (F'.connection t).NonnegativeCurvatureOperator x :=
    (F.ulift_nonnegativeCurvatureOperator_iff t x).mpr (hoperator x.down)
  have hRic (x : ULift.{u} M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ (F'.connection t).ricci x v v :=
    ((F'.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n _ _ _) x (hop x) v).1
  apply hν.trans_le
  apply ge_of_tendsto ((F'.metric t).tendsto_asymptoticVolumeRatio
    (F'.connection t) hn hc hRic (ULift.up p))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  have hv : ENNReal.ofReal (ν * r ^ n) ≤
      (F'.metric t).volumeMeasure ((F'.metric t).ball (ULift.up p) r) := by
    simpa only [F', ulift_volumeMeasure_ball] using hvolume r hr
  have h := ENNReal.toReal_mono
    ((F'.metric t).ball_volume_ne_top_of_metricComplete hc _ _) hv
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hν.le (pow_nonneg hr.le n))] using h

end PoincareConjecture.RicciFlow

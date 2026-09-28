import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.CompactRays
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RayLimits











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

open Splitting (segmentComparisonCosine)

variable {X : Type*} [MetricSpace X] {p : X}

def rayExtension (γ : basedMinimizingRays p) (t : ℝ) : X := γ.1 t.toNNReal

theorem rayExtension_zero (γ : basedMinimizingRays p) : rayExtension γ 0 = p := by
  simpa only [rayExtension, Real.toNNReal_zero] using γ.2.1

theorem rayExtension_dist (γ : basedMinimizingRays p)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (rayExtension γ s) (rayExtension γ t) = |s - t| := by
  rw [rayExtension, rayExtension, γ.2.2.dist_eq]
  change |(s.toNNReal : ℝ) - (t.toNNReal : ℝ)| = _
  rw [Real.coe_toNNReal s hs, Real.coe_toNNReal t ht]


def RayComparison (p : X) : Prop :=
  ∀ γ η : basedMinimizingRays p, ∀ a b : ℝ, 0 < a → 0 < b →
    ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
      s ^ 2 + t ^ 2 - 2 * s * t *
        segmentComparisonCosine (rayExtension γ) (rayExtension η) a b ≤
          dist (rayExtension γ s) (rayExtension η t) ^ 2


def asymptoticRayDistance (γ η : basedMinimizingRays p) : ℝ :=
  limUnder atTop (fun L : ℝ => dist (rayExtension γ L) (rayExtension η L) / L)

theorem tendsto_asymptoticRayDistance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    Tendsto (fun L : ℝ => dist (rayExtension γ L) (rayExtension η L) / L)
      atTop (𝓝 (asymptoticRayDistance γ η)) := by
  obtain ⟨q, _, hq⟩ := exists_homogeneous_ray_distance_limit
    (rayExtension γ) (rayExtension η)
    ((rayExtension_zero γ).trans (rayExtension_zero η).symm)
    (fun s hs t ht => rayExtension_dist γ hs ht)
    (fun s hs t ht => rayExtension_dist η hs ht) (hcomparison γ η)
  have h := (hq 1 1 zero_lt_one zero_lt_one).2
  simp only [one_mul] at h
  exact tendsto_nhds_limUnder ⟨_, h⟩

theorem asymptoticRayDistance_self (hcomparison : RayComparison p)
    (γ : basedMinimizingRays p) : asymptoticRayDistance γ γ = 0 := by
  apply tendsto_nhds_unique (tendsto_asymptoticRayDistance hcomparison γ γ)
  simpa only [dist_self, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))

theorem asymptoticRayDistance_comm (γ η : basedMinimizingRays p) :
    asymptoticRayDistance γ η = asymptoticRayDistance η γ := by
  unfold asymptoticRayDistance
  congr 1
  funext L
  rw [dist_comm]

theorem asymptoticRayDistance_triangle (hcomparison : RayComparison p)
    (γ η ζ : basedMinimizingRays p) :
    asymptoticRayDistance γ ζ ≤ asymptoticRayDistance γ η + asymptoticRayDistance η ζ := by
  apply le_of_tendsto_of_tendsto
    (tendsto_asymptoticRayDistance hcomparison γ ζ)
    ((tendsto_asymptoticRayDistance hcomparison γ η).add
      (tendsto_asymptoticRayDistance hcomparison η ζ))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [← add_div]
  exact div_le_div_of_nonneg_right (dist_triangle _ _ _) hL.le

theorem asymptoticRayDistance_le_dist_one (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    asymptoticRayDistance γ η ≤ dist (γ.1 1) (η.1 1) := by
  apply le_of_tendsto (tendsto_asymptoticRayDistance hcomparison γ η)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have h := hcomparison γ η L L hLpos hLpos 1 ⟨zero_le_one, hL⟩ 1 ⟨zero_le_one, hL⟩
  have heq : (1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 *
      segmentComparisonCosine (rayExtension γ) (rayExtension η) L L =
      (dist (rayExtension γ L) (rayExtension η L) / L) ^ 2 := by
    unfold segmentComparisonCosine
    field_simp
    ring
  rw [heq] at h
  simp only [rayExtension, Real.toNNReal_one] at h
  have hnonneg := div_nonneg (dist_nonneg (x := rayExtension γ L)
    (y := rayExtension η L)) hLpos.le
  dsimp only [rayExtension] at hnonneg ⊢
  nlinarith [dist_nonneg (x := γ.1 1) (y := η.1 1)]


@[instance_reducible] def asymptoticRayPseudoMetric (hcomparison : RayComparison p) :
    PseudoMetricSpace (basedMinimizingRays p) where
  dist := asymptoticRayDistance
  dist_self := asymptoticRayDistance_self hcomparison
  dist_comm := asymptoticRayDistance_comm
  dist_triangle := asymptoticRayDistance_triangle hcomparison

end Poincare.AncientVolume.ScalarRatio

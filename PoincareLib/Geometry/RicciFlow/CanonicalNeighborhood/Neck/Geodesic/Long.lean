import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Minimality
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Alignment

/-!
# Long-neck axial speed and alignment

The metric-jet producer supplies a scalar acceleration bound and an ambient
axial-pairing error. This file consumes those bounds together with intrinsic
minimality. The constants are written in scale-aware form, so the analytic
consumer is uniform in the neck scale.
-/

set_option autoImplicit false

open Set
open scoped InnerProductSpace Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.EpsilonNeck

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

/- The scale-aware real-variable consumer of the interval estimate. -/
theorem long_scaled_velocity_lower_bound_of_controls
    {f v acc : ℝ → ℝ} {L r ε α C δ : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hL : r / (100 * ε) < L)
    (hpos : 0 < (r * Real.sqrt (1 + ε))⁻¹ -
      C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε)))
    (hquality : 1 - α ≤ r * ((r * Real.sqrt (1 + ε))⁻¹ -
      C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε))))
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
      a ≤ b → b - a ≤ r * Real.sqrt (1 + ε) * (|f b - f a| + C))
    (horient : f 0 < f L) :
    ∀ t ∈ Icc 0 L, 1 - α ≤ r * v t := by
  have hlow := long_scaled_velocity_lower_bound hr hε hεhalf hL hf hv hacc hmin
    horient hpos
  intro t ht
  have hvt := hlow t ht
  have hmul := mul_le_mul_of_nonneg_left hvt hr.le
  nlinarith [hquality, hmul]

/- The same estimate with the intrinsic neck minimality interface exposed.
The two ENNReal inequalities are the exact segment and competitor statements;
the bridge to the real interval estimate is proved in `Geodesic.Minimality`.
-/
theorem long_scaled_velocity_lower_bound_of_intrinsic_minimality
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {f v acc : ℝ → ℝ} {L r ε α C δ : ℝ}
    (g : RiemannianMetric 3 M) (U : Set M)
    {x : ℝ → M}
    (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hL : r / (100 * ε) < L)
    (hpos : 0 < (r * Real.sqrt (1 + ε))⁻¹ -
      C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε)))
    (hquality : 1 - α ≤ r * ((r * Real.sqrt (1 + ε))⁻¹ -
      C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε))))
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hC : 0 ≤ C)
    (hsegment : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → ENNReal.ofReal (b - a) ≤
        intrinsicEDist g U (x a) (x b))
    (hcompetitor : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → intrinsicEDist g U (x a) (x b) ≤
        ENNReal.ofReal (r * Real.sqrt (1 + ε) *
          (|f b - f a| + C)))
    (horient : f 0 < f L) :
    ∀ t ∈ Icc 0 L, 1 - α ≤ r * v t := by
  have hmin := intrinsic_minimality_to_axial_competitor g U
    hr.le hε.le hC hsegment hcompetitor
  exact long_scaled_velocity_lower_bound_of_controls hr hε hεhalf hL hpos
    hquality hf hv hacc hmin horient

/- The public neck-specialized speed theorem. The only geometric inputs left
to the metric-jet producer are the scalar acceleration estimate and the two
intrinsic distance inequalities. -/
theorem long_neck_axial_speed_of_intrinsic_minimality
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {f v acc : ℝ → ℝ} {L α C δ : ℝ} {x : ℝ → M}
    (hL : N.scale / (100 * N.epsilon) < L)
    (hpos : 0 < (N.scale * Real.sqrt (1 + N.epsilon))⁻¹ -
      C / (N.scale / (200 * Real.sqrt N.epsilon)) -
      δ * (N.scale / (200 * Real.sqrt N.epsilon)))
    (hquality : 1 - α ≤ N.scale *
      ((N.scale * Real.sqrt (1 + N.epsilon))⁻¹ -
        C / (N.scale / (200 * Real.sqrt N.epsilon)) -
        δ * (N.scale / (200 * Real.sqrt N.epsilon))))
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hC : 0 ≤ C)
    (hsegment : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → ENNReal.ofReal (b - a) ≤
        intrinsicEDist g N.carrier (x a) (x b))
    (hcompetitor : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → intrinsicEDist g N.carrier (x a) (x b) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) *
          (|f b - f a| + C)))
    (horient : f 0 < f L) :
    ∀ t ∈ Icc 0 L, 1 - α ≤ N.scale * v t := by
  exact long_scaled_velocity_lower_bound_of_intrinsic_minimality g N.carrier
    N.scale_pos N.epsilon_pos N.epsilon_lt_half hL hpos hquality hf hv hacc hC
    hsegment hcompetitor horient

/- The neck-level interface for the metric-jet consumer. `η` measures the
quadratic pullback error and the axial pairing error in the ambient tangent
space. -/
theorem norm_sub_le_of_long_neck_controls
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u e : ℝ → E} {v : ℝ → ℝ} {L r α β η : ℝ}
    (hα : 0 ≤ α)
    (hunit : ∀ t ∈ Icc 0 L, ‖u t‖ = 1)
    (hquad : ∀ t ∈ Icc 0 L, |‖e t‖ ^ 2 - 1| ≤ η)
    (hpair : ∀ t ∈ Icc 0 L, |⟪u t, e t⟫_ℝ - r * v t| ≤ η)
    (hvel : ∀ t ∈ Icc 0 L, 1 - β ≤ r * v t)
    (hquality : 2 * β + 3 * η ≤ α ^ 2) :
    ∀ t ∈ Icc 0 L, ‖u t - e t‖ ≤ α := by
  intro t ht
  have hu := hunit t ht
  have hq := hquad t ht
  have hp := hpair t ht
  have hv := hvel t ht
  have hsq := norm_sub_sq_real (u t) (e t)
  have heupper : ‖e t‖ ^ 2 ≤ 1 + η := by
    have h := (abs_le.mp hq).2
    linarith
  have hinner : 1 - β - η ≤ ⟪u t, e t⟫_ℝ := by
    have h := (abs_le.mp hp).1
    linarith
  have hsq' : ‖u t - e t‖ ^ 2 ≤ α ^ 2 := by
    rw [hu] at hsq
    nlinarith [heupper, hinner, hquality]
  exact (sq_le_sq₀ (norm_nonneg _) hα).mp hsq'

end PoincareMT.EpsilonNeck

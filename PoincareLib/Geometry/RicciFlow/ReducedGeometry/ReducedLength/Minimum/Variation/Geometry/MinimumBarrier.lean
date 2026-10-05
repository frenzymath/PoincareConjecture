import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.TimeSupport.RegularPath
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.CurvatureMinimum
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Continuity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Comparison

/-!
# The sharp ancient-surface minimum bound

The surface index estimate and stationary-tail support use the same smooth
free-endpoint minimizer. Their combination gives the upper differential
inequality for the spatial infimum. Continuity and the initial zero limit
then give the sharp bound without a reduced-volume theory assumption.

Morgan--Tian, Theorem 7.10 and Claim 7.11, pp. 154--156.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareMT.ReducedLengthMinimum

theorem stationary_support_derivative_le {τ R m : ℝ} (hτ : 0 < τ)
    (hcurvature : τ * R + m ≤ 2) :
    R / 2 - m / (2 * τ) ≤ (1 - m) / τ := by
  apply (mul_le_mul_iff_right₀ hτ).mp
  have hleft : τ * (R / 2 - m / (2 * τ)) = (τ * R - m) / 2 := by
    field_simp [hτ.ne']
    <;> ring
  have hright : τ * ((1 - m) / τ) = 1 - m := by
    field_simp [hτ.ne']
  rw [hleft, hright]
  linarith

end PoincareMT.ReducedLengthMinimum

namespace PoincareMT.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- The actual minimizing path supplies a right upper support satisfying the
sharp surface differential inequality. -/
theorem exists_right_time_upper_support_le_one (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (b : ℝ → ℝ) (d : ℝ), b τ = K.spatialReducedLengthInfimum p τ ∧
      HasDerivAt b d τ ∧
      (∀ u : ℝ, τ ≤ u → K.spatialReducedLengthInfimum p u ≤ b u) ∧
      d ≤ (1 - K.spatialReducedLengthInfimum p τ) / τ := by
  obtain ⟨q, S, E, hq0, haction, hmin, heuler, hterminal⟩ :=
    K.exists_spatial_minimizing_sqrtRegularPath p hτ
  have hcurvature := K.curvature_add_minimum_le_two hτ q S E
    (fun r hr => hmin r (hr.trans hq0)) heuler hterminal haction
  obtain ⟨b, hb, hd, hsupport⟩ :=
    K.right_time_upper_support_of_sqrtRegularPath p hτ q S hq0 haction
  exact ⟨b, _, hb, hd, hsupport, stationary_support_derivative_le hτ hcurvature⟩

/-- The spatial reduced-length infimum of an ancient surface is at most one,
from the original frozen ancient-solution hypotheses alone. -/
theorem spatialReducedLengthInfimum_le_one (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) : K.spatialReducedLengthInfimum p τ ≤ 1 := by
  apply le_of_approximate_upper_barriers
    (K.continuousOn_spatialReducedLengthInfimum p) ?_ ?_ hτ
  · intro ε hε
    have hopen : (0 : ℝ) ∈ Iio (1 + ε) := by
      change 0 < 1 + ε
      linarith
    filter_upwards [(K.tendsto_spatialReducedLengthInfimum_zero p).eventually
      (Iio_mem_nhds hopen)] with s hs
    exact hs.le
  · intro t ht ε hε
    obtain ⟨b, d, hb, hd, hsupport, hbound⟩ :=
      K.exists_right_time_upper_support_le_one p ht
    refine ⟨b, d, hb, hd, ?_, by linarith⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hsupport s (le_of_lt hs)

end PoincareMT.AncientKappaSolution

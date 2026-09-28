import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.TimeSupport.RegularPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.CurvatureMinimum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Comparison

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum

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

end PoincareConjecture.ReducedLengthMinimum

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

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

end PoincareConjecture.AncientKappaSolution

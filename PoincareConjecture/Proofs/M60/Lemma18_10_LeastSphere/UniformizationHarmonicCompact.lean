import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M60

universe u

variable {M : Type u} [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem metricComplete_compact_surface (g : RiemannianMetric 2 M) : MetricComplete g := by
  unfold MetricComplete
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 2) M
  exact complete_of_compact

omit [T3Space M] in


theorem exists_sectionalCurvature_bound_compact_surface
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g) :
    ∃ K : ℝ, 0 < K ∧ ∀ x (v w : TangentSpace (𝓡 2) x),
      |D.sectionalCurvature x v w| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    D.continuous_scalarCurvature.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x v w
  by_cases hgram : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0
  · simp only [LeviCivitaData.sectionalCurvature, hgram, div_zero, abs_zero]
    positivity
  · rw [D.sectionalCurvature_eq_half_scalarCurvature x v w hgram, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb : |D.scalarCurvature x| ≤ |C| := by
      exact (Real.norm_eq_abs _ ▸ hC x (mem_univ x)).trans (le_abs_self C)
    calc
      |D.scalarCurvature x| / 2 ≤ |C| / 2 := div_le_div_of_nonneg_right hb (by norm_num)
      _ ≤ |C| + 1 := by linarith [abs_nonneg C]




theorem exists_harmonic_lift_compact_surface
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g) (p : M) :
    ∃ r C H : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < H ∧
      Nonempty (RiemannianMetric.UniformHarmonicLift g p r C H) := by
  obtain ⟨K, hK, hsec⟩ := exists_sectionalCurvature_bound_compact_surface g D
  obtain ⟨r, C, H, hr, hC, hH, h⟩ :=
    RiemannianMetric.exists_uniform_harmonic_lift (by norm_num : 2 ≤ 2) hK
  exact ⟨r, C, H, hr, hC, hH, h g D (metricComplete_compact_surface g) hsec p⟩

end PoincareConjecture.M60

end

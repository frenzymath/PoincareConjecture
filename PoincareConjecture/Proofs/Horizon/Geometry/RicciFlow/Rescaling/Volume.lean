import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure

set_option autoImplicit false

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem rescaledMetric_ball_allDimensions (g : RiemannianMetric n M)
    (c : ℝ) (hc : 0 < c) (x : M) (r : ℝ) :
    (rescaledMetric g c hc).ball x r = g.ball x (r / Real.sqrt c) := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hne : ENNReal.ofReal (Real.sqrt c) ≠ 0 := (ENNReal.ofReal_pos.mpr hsqrt).ne'
  ext y
  simp only [RiemannianMetric.ball, Set.mem_ofPred_eq, rescaledMetric_edist,
    ENNReal.ofReal_div_of_pos hsqrt]
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

end PoincareConjecture

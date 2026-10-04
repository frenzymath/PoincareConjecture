import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.SquareTime

/-!
# Compatibility of the coordinate metric and connection

The algebraic chart connection is torsion free and preserves the spatial
metric. These identities are the hypotheses of the coordinate second variation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped ContDiff

namespace PoincareMT.ReducedLengthMinimum.Variation.Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Symmetry of the metric makes its Koszul connection torsion free. -/
theorem chartConnection_symm
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v) (v w : E) :
    chartConnection G z v w = chartConnection G z w v := by
  have heq : chartConnectionCovector G z v w = chartConnectionCovector G z w v := by
    ext u
    rw [chartConnectionCovector_apply, chartConnectionCovector_apply,
      fderiv_bilinear_symm G z hG hsym (0, u) v w]
    ring
  simp only [chartConnection, heq]

/-- The spatial derivative of the metric is the sum of its two connection terms. -/
theorem chartConnection_metric_compatibility
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (v w u : E) :
    fderiv ℝ G z (0, v) w u =
      G z (chartConnection G z v w) u + G z w (chartConnection G z v u) := by
  rw [hsym.self_of_nhds w (chartConnection G z v u),
    chartConnection_pairing G z hpos, chartConnection_pairing G z hpos,
    fderiv_bilinear_symm G z hG hsym (0, v) u w]
  ring

end PoincareMT.ReducedLengthMinimum.Variation.Frame

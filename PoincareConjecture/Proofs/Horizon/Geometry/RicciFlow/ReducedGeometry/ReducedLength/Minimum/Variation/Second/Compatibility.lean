import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.SquareTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

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

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame

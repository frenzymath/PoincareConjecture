import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.InitialJacobianGram
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.InitialTime.InitialJacobianCalculus

/-!
# The initial normalized actual exponential Jacobian

The actual scaled Gram matrix tends to 4I. Taking its determinant
and nonnegative square root gives the factor 2 to the dimension,
including dimension zero. Morgan-Tian Proposition 6.78, pp. 142-144.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The actual metric Jacobian divided by square time to the dimension
tends to 2^n on any positive surviving prefix. No zero-time supplied
Jacobian convention is assumed, Proposition 6.78, pp. 142-144. -/
theorem tendsto_exponentialJacobian_normalized_zero
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (b₀ : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner x (b₀ i) (b₀ j) =
      if i = j then 1 else 0)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    Tendsto (fun s : ℝ => exponentialJacobian E b₀ Z s / s ^ n) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 : ℝ) ^ n)) := by
  have h := M10.tendsto_scaled_sqrt_det
    (tendsto_exponentialGram_scaled_zero hM04 hM12 E b₀ horth hb hpos)
  convert h using 1
  funext s
  rw [exponentialJacobian_eq_sqrt_det]
  ring

end PoincareMT.M14

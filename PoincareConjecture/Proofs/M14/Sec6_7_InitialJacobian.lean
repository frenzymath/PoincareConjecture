import PoincareConjecture.Proofs.M14.Sec6_7_InitialJacobianGram
import PoincareConjecture.Proofs.M10.InitialJacobianCalculus

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

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

end PoincareConjecture.M14

import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Uniform

/-!
Adapted from Mapher `PoincareMT/Definitions/M15Noncollapsing.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

def M15GeneralizedNoncollapseAt
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (r₀ κ : ℝ) : Prop :=
  ∀ (r : ℝ), 0 < r → r ≤ r₀ →
    ∀ (x : (G.slices (G.spacetime.timeFunction p)).Point), x.val = p →
    ∀ (K : SpacetimeInterval)
      (C : Type u) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
      [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
      (_B : M15ActualBallCylinder G (G.spacetime.timeFunction p) x r K C),
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume
          (G.slices (G.spacetime.timeFunction p)).metricOnPoints
          ((G.slices (G.spacetime.timeFunction p)).metricOnPoints.ball x r)

/-!
For each tested point and scale, a provider supplies one actual M14 branch,
stable set, and Theorem 8.1 configuration.  Compact closure belongs to the
configuration's source-cylinder support; the target predicate remains the
ordinary volume statement above.
-/
structure M15ConfigurationProvider
    (G : GeneralizedLGeometryTransport n X time I)
    (Omega : Set G.Point)
    (taubar l₀ V r₀ : ℝ) : Prop where
  provide : ∀ (p : G.Point), p ∈ Omega →
    ∀ (r : ℝ), 0 < r → r ≤ r₀ →
    ∀ (x : (G.slices (G.spacetime.timeFunction p)).Point), x.val = p →
    ∀ (K : SpacetimeInterval)
      (C : Type u) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
      [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
      (B : M15ActualBallCylinder G (G.spacetime.timeFunction p) x r K C),
      ∃ E : M14ExponentialFamily G (G.spacetime.timeFunction p) x.val,
        Nonempty (M15Theorem81Configuration G
          (G.spacetime.timeFunction p) x E taubar l₀ V r K C B)

/-!
The useful target form of the provider implication keeps the fixed constant
visible.  The implication is a proposition, so the later proving theorem can
state it without defining a second hidden noncollapsing notion.
-/
def M15ProviderImpliesNoncollapse
    (G : GeneralizedLGeometryTransport n X time I)
    (Omega : Set G.Point)
    (taubar l₀ V r₀ κ : ℝ)
    (U : M15GeneralizedUniformData.{u} n taubar l₀ V) : Prop :=
  M15ConfigurationProvider G Omega taubar l₀ V r₀ →
    (κ = U.kappa ∧
      ∀ (p : G.Point) (_hp : p ∈ Omega),
        M15GeneralizedNoncollapseAt G p r₀ κ)

end PoincareMT

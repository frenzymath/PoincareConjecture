import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Cover
import PoincareLib.Geometry.Spacetime.Horizontal.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M14GeneralizedLGeometry.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are unchanged;
imports and module placement are adapted. See
`references/ricci-flow/mapher/generalized-noncollapse-port.json`. -/

/-!
# M14 actual spacetime paths and L-action

Morgan-Tian Definitions 6.1-6.2, pp. 105-106. The admissible class has
closed-interval continuity, interior C1 regularity, the actual clock and
horizontal velocity, and finite action. Finite infima and attained minima
are separate predicates. No completeness or minimizing existence is assumed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- The selected actual M11/M12 geometry used throughout M14. -/
structure GeneralizedLGeometryTransport (n : ℕ) (X : Type u)
    [TopologicalSpace X] (time : X → ℝ) (I : SpacetimeInterval) where
  spacetime : GeneralizedFlowSpacetime n X time I
  slices : ∀ t : ℝ, SpacetimeSliceGeometry spacetime t
  timeIntervals : SpacetimeIntervalSystem
  gaugeCover : SpacetimeGaugeCover spacetime timeIntervals
  leafwise : LeafwiseLeviCivitaFamily spacetime slices
  ricciEquation : IntrinsicGeneralizedRicciEquation leafwise

namespace GeneralizedLGeometryTransport

abbrev Point (G : GeneralizedLGeometryTransport n X time I) := G.spacetime.Point

abbrev Horizontal (G : GeneralizedLGeometryTransport n X time I) (p : G.Point) :=
  G.spacetime.Horizontal p

end GeneralizedLGeometryTransport

/-- The actual weighted scalar-plus-kinetic density. -/
noncomputable def M14RawLIntegrand (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (v : ∀ τ, G.Horizontal (γ τ)) (τ : ℝ) : ℝ :=
  Real.sqrt τ * (horizontalScalarCurvature G.leafwise (γ τ) +
    G.spacetime.horizontalMetric.inner (γ τ) (v τ) (v τ))

/-- An admissible generalized backward path with its actual derivative. -/
structure M14BackwardPath (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) where
  tau_nonneg : 0 ≤ τ₁
  tau_lt : τ₁ < τ₂
  base_time : G.spacetime.timeFunction x = T - τ₁
  endpoint_time : G.spacetime.timeFunction y = T - τ₂
  curve : ℝ → G.Point
  curve_start : curve τ₁ = x
  curve_end : curve τ₂ = y
  curve_time : ∀ τ ∈ Set.Icc τ₁ τ₂,
    G.spacetime.timeFunction (curve τ) = T - τ
  curve_continuous : ContinuousOn curve (Set.Icc τ₁ τ₂)
  curve_regular : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 curve
    (Set.Ioo τ₁ τ₂)
  horizontal_velocity : ∀ τ, G.Horizontal (curve τ)
  derivative_eq : ∀ τ ∈ Set.Ioo τ₁ τ₂,
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) curve τ (1 : ℝ) =
      -G.spacetime.timeVector (curve τ) + (horizontal_velocity τ).val
  action_integrable : IntervalIntegrable
    (M14RawLIntegrand G curve horizontal_velocity) MeasureTheory.volume τ₁ τ₂

noncomputable def M14BackwardLIntegrand (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) : ℝ → ℝ :=
  M14RawLIntegrand G p.curve p.horizontal_velocity

noncomputable def M14BackwardLAction (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) : ℝ :=
  ∫ τ in τ₁..τ₂, M14BackwardLIntegrand G p τ

def M14ActionSet (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) : Set ℝ :=
  {a | ∃ p : M14BackwardPath G T τ₁ τ₂ x y, M14BackwardLAction G p = a}

def M14FiniteValueDomain (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) : Prop :=
  (M14ActionSet G T τ₁ τ₂ x y).Nonempty ∧
    BddBelow (M14ActionSet G T τ₁ τ₂ x y)

def M14IsMinimizing {G : GeneralizedLGeometryTransport n X time I}
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) : Prop :=
  ∀ q : M14BackwardPath G T τ₁ τ₂ x y,
    M14BackwardLAction G p ≤ M14BackwardLAction G q

def M14AttainedDomain (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) : Prop :=
  ∃ p : M14BackwardPath G T τ₁ τ₂ x y, M14IsMinimizing p

/-- The raw action infimum; its mathematical use requires a finite-value domain. -/
noncomputable def M14ActionValue (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) : ℝ :=
  sInf (M14ActionSet G T τ₁ τ₂ x y)

/-- Morgan-Tian Definition 6.45: normalized reduced length at absolute time τ₂. -/
noncomputable def M14ReducedLengthValue (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ τ₂ : ℝ) (x y : G.Point) : ℝ :=
  M14ActionValue G T τ₁ τ₂ x y / (2 * Real.sqrt τ₂)

/-- Reduced length on actual spacetime: the endpoint clock fixes elapsed time. -/
noncomputable def M14ReducedLengthAt (G : GeneralizedLGeometryTransport n X time I)
    (T τ₁ : ℝ) (x q : G.Point) : ℝ :=
  M14ReducedLengthValue G T τ₁ (T - G.spacetime.timeFunction q) x q

/-- The backward time derivative at fixed compatible spatial coordinate. -/
noncomputable def M14BackwardTimeDerivative
    (G : GeneralizedLGeometryTransport n X time I)
    (f : G.Point → ℝ) (q : G.Point) : ℝ :=
  -(mvfderiv (spacetimeModel n) f q) (G.spacetime.timeVector q)

/-- The generalized Harnack density along an actual backward path. -/
noncomputable def M14GeneralizedHarnackDensity
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (scalarTimeDerivative : ℝ → ℝ) (s : ℝ) : ℝ :=
  -scalarTimeDerivative s -
    horizontalScalarCurvature G.leafwise (p.curve s) / s -
    2 * (mvfderiv (spacetimeModel n)
      (fun q : G.Point => horizontalScalarCurvature G.leafwise q) (p.curve s))
      (p.horizontal_velocity s).val +
    2 * horizontalRicci G.leafwise (p.curve s)
      (p.horizontal_velocity s) (p.horizontal_velocity s)

/-- The actual `K` integral used by the regular formulas. -/
noncomputable def M14GeneralizedKIntegral
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (scalarTimeDerivative : ℝ → ℝ) : ℝ :=
  ∫ s in τ₁..τ₂,
    s * Real.sqrt s * M14GeneralizedHarnackDensity G p scalarTimeDerivative s

end PoincareMT


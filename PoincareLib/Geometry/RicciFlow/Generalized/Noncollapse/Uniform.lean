import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential
import PoincareLib.Geometry.Riemannian.Measure.Calibrated

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M15Noncollapsing.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. This module retains the
unchanged generalized uniform service and its exact definition closure.
See `references/ricci-flow/mapher/generalized-noncollapse-port.json`. -/

/-!
# M15 noncollapsing data and predicates

Morgan--Tian, Theorem 8.1, pp. 169-176, and Theorem 8.10, pp. 176-177.
This file contains the actual configuration interfaces used by those two
results.  A configuration keeps one generalized spacetime, one M14
exponential branch, one fixed-time stable set, one based compatible cylinder,
and the three source estimates (`tau₀`, normalized reduced length, and
terminal image volume).  The constants are quantified before the flow and
configuration.  The compact statement is a separate interface and does not
reuse generalized-flow constants.

The Chapter 8 source is read together with the project corrections in
`reviews/errata/2026-09-13-reduced-length-source.md` and
`reviews/errata/2026-09-11-tensor-evolution.md`, and the repair contract in
`reviews/contracts/M15-repair-contract.md`.  In particular, the cylinder is
based on every point of the actual terminal ball, its curvature hypothesis is
on the full image (including endpoints), and the compact clause evaluates
only at times belonging to the supplied flow domain.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-! ### Actual based cylinders -/

/-!
An actual smooth source for a compatible cylinder need not itself be the
ambient slice type: an open metric ball has no automatic manifold instance in
the pinned library.  The source carrier is therefore an explicitly charted
manifold, together with an embedding whose range is exactly the selected
metric ball.  This is the source-ball condition and does not permit an
unrelated carrier or a center-only based identity.
-/
structure M15ActualBallCylinder
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C] where
  radius_pos : 0 < r
  interval_domain : K.domain = Set.Icc (T - r ^ 2) T
  base_mem : T ∈ K.domain
  embedding : CompatibleSpacetimeCylinder G.spacetime
    (G.timeIntervals.interval K) C
  metric : SpacetimeCylinderMetric embedding
  source_map : C → (G.slices T).Point
  source_map_embedding : Topology.IsEmbedding source_map
  source_map_range : Set.range source_map =
    (G.slices T).metricOnPoints.ball x r
  based : ∀ c : C,
    embedding.toSpacetime (⟨⟨T, base_mem⟩, c⟩) = (source_map c).val
  source_map_smooth :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ source_map Set.univ
  source_map_differential_injective : ∀ c,
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) source_map c)
  curvature_bound : ∀ s : (G.timeIntervals.interval K).Point, ∀ c : C,
    horizontalCurvatureNorm G.leafwise
      (embedding.toSpacetime (s, c)) ≤ r⁻¹ ^ 2

/-! ### Theorem 8.1 configuration -/

/-!
The normalized length is the M14 reduced-length field
`E.reduced_length Z (sqrt tau₀)`, not a bound on raw action.  The endpoint
volume is measured in the exact selected slice metric.  The stable set and
its endpoint map therefore cannot be replaced by an arbitrary open tangent
set or a chosen formal exponential.
-/
structure M15Theorem81Configuration
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point)
    (E : M14ExponentialFamily G T x.val)
    (taubar l₀ V : ℝ)
    (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    (B : M15ActualBallCylinder G T x r K C) where
  tau₀ : ℝ
  tau₀_pos : 0 < tau₀
  tau₀_le : tau₀ ≤ taubar
  radius_sq_le_tau₀ : r ^ 2 ≤ tau₀
  terminal_mem : T - tau₀ ∈ I.domain
  terminal_ball_compact :
    IsCompact (closure ((G.slices T).metricOnPoints.ball x r))
  stable : M14StableSet G T tau₀ x.val E
  W : Set (G.Horizontal x.val)
  W_open : IsOpen W
  W_subset_stable : W ⊆ stable.carrier
  normalized_reduced_length : ∀ Z, Z ∈ W →
    E.reduced_length Z (Real.sqrt tau₀) ≤ l₀
  terminal_image_volume : ENNReal.ofReal V ≤
    calibratedMetricVolume (G.slices (T - tau₀)).metricOnPoints
      (stable.endpoint_slice_map '' W)

/-!
The source estimate is stated directly on a configuration.  The ball on the
right is the same ball whose source range occurs in `B`; no independent
metric or carrier is available to the estimate.
-/
def M15Theorem81Estimate
    {G : GeneralizedLGeometryTransport n X time I}
    {T : ℝ} {x : (G.slices T).Point}
    {E : M14ExponentialFamily G T x.val}
    {taubar l₀ V r : ℝ} {K : SpacetimeInterval} {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    {B : M15ActualBallCylinder G T x r K C}
    (_configuration : M15Theorem81Configuration G T x E taubar l₀ V r K C B)
    (κ : ℝ) : Prop :=
  ENNReal.ofReal (κ * r ^ n) ≤
    calibratedMetricVolume (G.slices T).metricOnPoints
      ((G.slices T).metricOnPoints.ball x r)

/-!
Uniformity is explicit: `κ` is a field of the fixed-constant package and the
configuration quantifiers occur only after the generalized spacetime and all
of its M14 data.  The package carries this data directly, while every
estimate field is proposition-valued, so constructing it cannot hide an
admitted theorem in a helper definition.
-/
structure M15GeneralizedUniformData (n : ℕ) (taubar l₀ V : ℝ) where
  taubar_pos : 0 < taubar
  l₀_pos : 0 < l₀
  V_pos : 0 < V
  kappa : ℝ
  kappa_pos : 0 < kappa
  estimate : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval)
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point)
    (E : M14ExponentialFamily G T x.val)
    (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    (B : M15ActualBallCylinder G T x r K C),
    (configuration : M15Theorem81Configuration G T x E taubar l₀ V r K C B) →
      M15Theorem81Estimate configuration kappa

/-!
The generalized theorem quantifies the source constants before all geometric
objects.  It is the exact uniform conclusion of Theorem 8.1; no
`omega`/`T₀` parameters occur in this clause.
-/
def M15GeneralizedUniformTheorem (n : ℕ) : Prop :=
  ∀ (taubar l₀ V : ℝ), 0 < taubar → 0 < l₀ → 0 < V →
    Nonempty (M15GeneralizedUniformData.{u} n taubar l₀ V)

end PoincareMT

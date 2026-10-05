import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.ExponentialTheory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory

/-!
# Ordinary capture of generalized reduced geometry

The M08/M09/M10 providers and the generalized-to-ordinary capture interface
are ported unchanged from `PoincareMT/Statements/M14GeneralizedLGeometry.lean` at
Mapher revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
The reduced volume is taken over the actual stable exponential image.
Source: Morgan-Tian, Chapter 7 and Theorem 8.1, pp. 149-167, 169-171.
See `references/ricci-flow/mapher/generalized-noncollapse-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

noncomputable def M14ReducedVolumeOnStable
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (τ : ℝ)
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E) : ℝ :=
  ∫ q in H.endpoint_slice_map '' H.carrier,
    Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q.val)
    ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints

structure M14OrdinaryProviders (n : ℕ) : Prop where
  m08 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    Nonempty (LGeodesicTheory F T τmax)
  m09 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    LGeodesicTheory F T τmax → Nonempty (ReducedLengthDifferentialTheory F T τmax)
  m10 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    LGeodesicTheory F T τmax → ReducedLengthDifferentialTheory F T τmax →
    Nonempty (ReducedVolumeTheory F T τmax)

/-! Ordinary transport uses the same metric, the actual cylinder inverse,
and capture of paths starting in the selected part during the valid window.
Action, regularity, and volume comparisons are theorem conclusions. -/
structure M14OrdinaryCaptureData
    (G : GeneralizedLGeometryTransport n X time I)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    [T3Space C]
    [ConnectedSpace C] [SecondCountableTopology C]
    [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain) (T τmax : ℝ) where
  metric_eq : Set.EqOn F.metric g.metric K.domain
  point_map : G.Point → C
  point_map_on_cylinder : ∀ (s : (G.timeIntervals.interval K).Point) (c : C),
    point_map (e.toSpacetime (s, c)) = c
  point_map_continuous : ContinuousOn point_map (Set.range e.toSpacetime)
  path_map : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    ∀ p : M14BackwardPath G T τ₁ τ₂ x y,
      (∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime) →
      BackwardTimePath F T τ₁ τ₂
  path_start_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    (path_map τ₁ τ₂ x y p hcaptured).curve τ₁ = point_map x
  path_end_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    (path_map τ₁ τ₂ x y p hcaptured).curve τ₂ = point_map y
  path_curve_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    ∀ s ∈ Set.Icc τ₁ τ₂,
      point_map (p.curve s) = (path_map τ₁ τ₂ x y p hcaptured).curve s
  path_capture_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    ∀ (s : ℝ) (hs : s ∈ Set.Icc τ₁ τ₂),
      e.toSpacetime
        ((⟨T - s, (path_map τ₁ τ₂ x y p hcaptured).time_mem s hs⟩,
          (path_map τ₁ τ₂ x y p hcaptured).curve s)) = p.curve s
  path_lift : ∀ (τ₁ τ₂ : ℝ) (q : BackwardTimePath F T τ₁ τ₂),
    ∃ p : M14BackwardPath G T τ₁ τ₂
      (e.toSpacetime
        ((⟨T - τ₁, q.time_mem τ₁
          ⟨le_rfl, le_of_lt q.ordered⟩⟩, q.curve τ₁)))
      (e.toSpacetime
        ((⟨T - τ₂, q.time_mem τ₂
          ⟨le_of_lt q.ordered, le_rfl⟩⟩, q.curve τ₂))),
      ∀ (s : ℝ) (hs : s ∈ Set.Icc τ₁ τ₂),
        e.toSpacetime ((⟨T - s, q.time_mem s hs⟩, q.curve s)) = p.curve s
  capture_from_start : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    τ₂ ≤ τmax → x ∈ Set.range e.toSpacetime →
    ∀ p : M14BackwardPath G T τ₁ τ₂ x y,
      ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime

structure M14OrdinaryCaptureOutput
    (G : GeneralizedLGeometryTransport n X time I)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    [T3Space C]
    [ConnectedSpace C] [SecondCountableTopology C]
    [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain) (T τmax : ℝ)
    (D : M14OrdinaryCaptureData G C K e g F T τmax) where
  L : LGeodesicTheory F T τmax
  Dlength : ReducedLengthDifferentialTheory F T τmax
  V : ReducedVolumeTheory F T τmax
  action_transport : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hcaptured : ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime),
      backwardLLength F T τ₁ τ₂
      (D.path_map τ₁ τ₂ x y p hcaptured).curve = M14BackwardLAction G p
  captured_action_value_eq : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
    x ∈ Set.range e.toSpacetime → y ∈ Set.range e.toSpacetime →
    M14ActionValue G T τ₁ τ₂ x y =
      sInf {a | ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
        (∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime) ∧
        M14BackwardLAction G p = a}
  reduced_length_transport : ∀ (τ : ℝ) (x y : G.Point),
    0 < τ → τ ≤ τmax →
    G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction y = T - τ →
    x ∈ Set.range e.toSpacetime → y ∈ Set.range e.toSpacetime →
    M14ReducedLengthValue G T 0 τ x y =
      reducedLength F T (D.point_map x) (D.point_map y) τ
  minimizing_transport : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point), τ₂ ≤ τmax →
    x ∈ Set.range e.toSpacetime →
    ∀ (p : M14BackwardPath G T τ₁ τ₂ x y)
      (hcaptured : ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime),
      M14IsMinimizing p ↔
        IsMinimizingBackwardLPath F T τ₁ τ₂ (D.path_map τ₁ τ₂ x y p hcaptured)
  regular_locus_transport : ∀ (τ : ℝ) (x : G.Point), 0 < τ → τ < τmax →
    x ∈ Set.range e.toSpacetime →
    ∀ (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
      (Z : G.Horizontal x), Z ∈ H.carrier →
    (Z, Real.sqrt τ) ∈ M14JointDomain G E →
    ∀ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z), M14IsMinimizing p →
    (∀ s ∈ Set.Icc 0 τ, p.curve s = E.gamma Z (Real.sqrt s)) →
    ∀ hcaptured : ∀ s ∈ Set.Icc 0 τ, p.curve s ∈ Set.range e.toSpacetime,
      ∃ r : ReducedLengthRegularPoint F T τmax
          (D.point_map x) (D.point_map (H.endpoint_map Z)) τ,
        r.path.curve = (D.path_map 0 τ x (H.endpoint_map Z) p hcaptured).curve
  volume_transport : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    M14ReducedVolumeOnStable G T x τ H =
      reducedVolumeOn F T (D.point_map x) τ
        (D.point_map '' ((fun q => q.val) ''
          (H.endpoint_slice_map '' H.carrier)))
  endpoint_image_captured : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    (fun q => q.val) '' (H.endpoint_slice_map '' H.carrier) ⊆
      Set.range e.toSpacetime
  slice_measure_transport : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      (H.endpoint_slice_map '' H.carrier) =
      calibratedMetricVolume (F.metric (T - τ))
        (D.point_map '' ((fun q => q.val) ''
          (H.endpoint_slice_map '' H.carrier)))
  /-- Completeness and capture identify the exact stable image with the
      ordinary full-measure regular locus (Proposition 7.5). -/
  captured_stable_image_full_measure : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ < τmax → x ∈ Set.range e.toSpacetime →
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      ({q | q.val ∈ Set.range e.toSpacetime} \
        (H.endpoint_slice_map '' H.carrier)) = 0
  /-- The actual cylinder metric preserves volume on each measurable
      captured subset, including the terminal W images used by M15. -/
  captured_slice_measure_transport : ∀ (τ : ℝ), 0 < τ → τ < τmax →
    ∀ A : Set (G.slices (T - τ)).Point, MeasurableSet A →
    (fun q => q.val) '' A ⊆ Set.range e.toSpacetime →
      calibratedMetricVolume (G.slices (T - τ)).metricOnPoints A =
        calibratedMetricVolume (F.metric (T - τ))
          (D.point_map '' ((fun q => q.val) '' A))

def M14OrdinaryCaptureStatement
    (G : GeneralizedLGeometryTransport n X time I)
    (O : M14OrdinaryProviders.{u} n) : Prop :=
  ∀ (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [ConnectedSpace C] [T3Space C]
    [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain)
    (T τmax : ℝ) (hT : T ∈ K.domain) (hτ : 0 < τmax)
    (hK : Set.Icc (T - τmax) T ⊆ K.domain)
    (hcurv : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)),
    ∀ capture : M14OrdinaryCaptureData G C K e g F T τmax,
      ∃ out : M14OrdinaryCaptureOutput G C K e g F T τmax capture,
        out.L = Classical.choice (O.m08 C K.domain F T τmax hT hτ hK hcurv) ∧
        out.Dlength = Classical.choice (O.m09 C K.domain F T τmax hT hτ hK hcurv out.L) ∧
        out.V = Classical.choice (O.m10 C K.domain F T τmax hT hτ hK hcurv out.L out.Dlength)

end PoincareMT

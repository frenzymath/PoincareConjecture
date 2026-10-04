import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.RicciFlow.Compactness.Carrier
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Pointed flows on varying carriers

The interfaces keep the carriers of a sequence explicit. A `FlowCarrier`
packages the topological and smooth structures needed by the
fixed-carrier Ricci-flow definition, while `BasedFlow` adds the time-zero base
point.  The compactness statement carries a volume measure with each based
flow and requires it to agree with the n-dimensional Hausdorff measure of the
selected time-zero metric.  This makes the source volume convention explicit.

The declarations are ported from the reviewed snapshot in
`contracts/definitions/ricci-flow/PointedRicciFlowCompactness.lean`, from
Mapher06/Poincare-MorganTian at `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`.
The carrier declarations are in `Compactness.Carrier`; mathematical definitions
and declaration names are unchanged.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The order-`r` derivative seminorm of a scalar coordinate coefficient. -/
noncomputable def MetricJet {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (r : ℕ) (f : α → ℝ) (_s : Set α) (x : α) :=
  iteratedFDeriv ℝ r f x

abbrev FlowCarrier.metric {n : ℕ} (C : FlowCarrier n) :=
  @RiemannianMetric n C.carrier C.topologicalSpace C.chartedSpace C.isManifold

/-- A based Ricci flow on one carrier, with its time-zero basepoint. -/
structure BasedFlow (n : ℕ) (T' T : ℝ) (C : FlowCarrier n) where
  base : C.carrier
  flow : @RicciFlow n C.carrier C.topologicalSpace C.chartedSpace C.isManifold
    (Set.Ioo T' T)
  volumeMeasure : @MeasureTheory.Measure C.carrier C.measurableSpace
  /-- The spacetime vector field in the ordinary product-flow specialization.
  The next field forces its spatial part to vanish, so this is the canonical
  increasing-time vector field and the stored RicciFlow equation is exactly
  the generalized equation in product coordinates. -/
  spacetimeVectorField : ∀ _t : ℝ, ∀ x : C.carrier, ℝ × C.tangent x
  spacetimeVectorField_time :
    ∀ t x, (spacetimeVectorField t x).1 = 1
  spacetimeVectorField_spatial_zero :
    ∀ t x, (spacetimeVectorField t x).2 = 0

namespace FlowCarrier

noncomputable def coordinateCoefficient {n : ℕ} (C : FlowCarrier n) (q : C.carrier)
    (B : ∀ _t : ℝ, ∀ x : C.carrier, C.tangent x → C.tangent x → ℝ)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  let A := mfderiv (𝓡 n) (𝓡 n) c.symm p.2
  B p.1 (c.symm p.2)
    (A (EuclideanSpace.basisFun (Fin n) ℝ a))
    (A (EuclideanSpace.basisFun (Fin n) ℝ b))

/-- The metric ball used by the zero-time slice of a based flow. -/
def metricBall {n : ℕ} (C : FlowCarrier n) (g : C.metric) (x : C.carrier)
    (r : ℝ) : Set C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  RiemannianMetric.ball g x r

noncomputable def metricInner {n : ℕ} (C : FlowCarrier n) (g : C.metric) (x : C.carrier)
    (v w : C.tangent x) : ℝ :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  g.inner x v w

noncomputable def metricNorm {n : ℕ} (C : FlowCarrier n) (g : C.metric) (x : C.carrier)
    (v : C.tangent x) : ℝ :=
  Real.sqrt (C.metricInner g x v v)

/-- The Hausdorff n-measure of a selected Riemannian metric. -/
noncomputable def metricHausdorffVolume {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    @MeasureTheory.Measure C.carrier C.measurableSpace :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
  MeasureTheory.Measure.hausdorffMeasure (n : ℝ)

/- The extended metric induced by a slice, exposed as a value so that
  completeness-transfer lemmas can quantify over a family of slices. -/
noncomputable def metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    EMetricSpace C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier

theorem preconnected_metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    @PreconnectedSpace C.carrier
      (C.metricEMetricSpace g).toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : EMetricSpace C.carrier := C.metricEMetricSpace g
  change @PreconnectedSpace C.carrier C.topologicalSpace
  exact ⟨C.connected.isPreconnected⟩

/-- Completeness of the induced extended metric for a selected slice. -/
def metricComplete {n : ℕ} (C : FlowCarrier n) (g : C.metric) : Prop :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
  CompleteSpace C.carrier

end FlowCarrier

namespace BasedFlow

def volumeCompatible {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) : Prop :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  F.volumeMeasure = C.metricHausdorffVolume (F.flow.metric 0)

def zeroBall {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (r : ℝ) : Set C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  C.metricBall (F.flow.metric 0) F.base r

def ballAt {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (t r : ℝ) : Set C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  C.metricBall (F.flow.metric t) F.base r

noncomputable def zeroBallVolume {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (r : ℝ) : ℝ≥0∞ :=
  F.volumeMeasure (F.zeroBall r)

end BasedFlow

/-- A smooth, time-preserving embedding between possibly different carriers. -/
structure SmoothSpacetimeEmbedding {n : ℕ} {T' T : ℝ}
    {C D : FlowCarrier n} (F : BasedFlow n T' T C) (G : BasedFlow n T' T D)
    (domain : Set (ℝ × C.carrier)) where
  toFun : ℝ × C.carrier → ℝ × D.carrier
  time_preserving : ∀ t x, (toFun (t, x)).1 = t
  injective_on : Set.InjOn toFun domain
  inverse : ℝ × D.carrier → ℝ × C.carrier
  left_inverse : ∀ p ∈ domain, inverse (toFun p) = p
  right_inverse : ∀ q ∈ toFun '' domain, toFun (inverse q) = q
  smooth_on :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      toFun domain
  smooth_inverse_on :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      inverse (toFun '' domain)
  vector_field_compatible :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    let ψ : ∀ _t : ℝ, C.carrier → D.carrier := fun t x ↦ (toFun (t, x)).2
    ∀ t x,
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s ↦ (toFun (s, x)).2) t 1 +
        mfderiv (𝓡 n) (𝓡 n) (ψ t) x (F.spacetimeVectorField t x).2) =
        (G.spacetimeVectorField t (ψ t x)).2

/-- A smooth, time-preserving embedding of a zero-time ball through an interval. -/
abbrev SpacetimeEmbedding {n : ℕ} {T' T : ℝ}
    {C D : FlowCarrier n} (F : BasedFlow n T' T C) (G : BasedFlow n T' T D)
    (A : ℝ) (I : Set ℝ) :=
  SmoothSpacetimeEmbedding F G (I ×ˢ F.zeroBall A)

noncomputable def BasedFlow.metricAt {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (t : ℝ) : C.metric :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  F.flow.metric t

/-- Uniform curvature control on the image domain of a spacetime embedding. -/
def CurvatureBoundOn {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    {D : FlowCarrier n} (F : BasedFlow n T' T C) (G : BasedFlow n T' T D)
    (A : ℝ) (I : Set ℝ) (e : SpacetimeEmbedding F G A I) (K : ℝ) : Prop :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  0 ≤ K ∧ ∀ t ∈ I, ∀ x ∈ F.zeroBall A,
    (G.flow.connection t).curvatureTensorNorm ((e.toFun (t, x)).2) ≤ K

end PoincareMT

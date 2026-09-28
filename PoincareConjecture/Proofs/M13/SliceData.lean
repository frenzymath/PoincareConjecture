import PoincareConjecture.Definitions.M11SpacetimeSlices

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

structure SliceData (F : GeneralizedFlowSpacetime n X time I) (U : Set F.Point) where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) U
  isManifold : IsManifold (𝓡 n) ∞ U
  t3Space : T3Space U
  secondCountable : SecondCountableTopology U
  measurableSpace : MeasurableSpace U
  borelSpace : BorelSpace U
  inclusion_smooth : ContMDiff (𝓡 n) (spacetimeModel n) ∞ (Subtype.val : U → F.Point)
  inclusion_embedding : Topology.IsEmbedding (Subtype.val : U → F.Point)
  inclusion_differential_injective : ∀ x : U,
    Function.Injective (mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : U → F.Point) x)
  tangentEquiv : ∀ x : U, TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal x.val
  tangentEquiv_eq : ∀ x v, (tangentEquiv x v).val =
    mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : U → F.Point) x v
  metric : RiemannianMetric n U
  metric_eq : ∀ x v w, metric.inner x v w =
    F.horizontalMetric.inner x.val (tangentEquiv x v) (tangentEquiv x w)

namespace SliceData

variable {F : GeneralizedFlowSpacetime n X time I} {U V : Set F.Point}

abbrev Point (_D : SliceData F U) := U

instance (D : SliceData F U) : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.Point :=
  D.chartedSpace

instance (D : SliceData F U) : IsManifold (𝓡 n) ∞ D.Point := D.isManifold

instance (D : SliceData F U) : T3Space D.Point := D.t3Space

instance (D : SliceData F U) : SecondCountableTopology D.Point := D.secondCountable

instance (D : SliceData F U) : MeasurableSpace D.Point := D.measurableSpace

instance (D : SliceData F U) : BorelSpace D.Point := D.borelSpace

noncomputable abbrev metricOnPoints (D : SliceData F U) : RiemannianMetric n D.Point :=
  D.metric

noncomputable def transport (D : SliceData F U) (h : U = V) : SliceData F V := h ▸ D

noncomputable def identification (D : SliceData F U) (h : U = V) :
    Diffeomorph (𝓡 n) (𝓡 n) D.Point (D.transport h).Point ∞ := by
  subst V
  exact Diffeomorph.refl (𝓡 n) D.Point ∞

theorem identification_val (D : SliceData F U) (h : U = V) (x : D.Point) :
    (D.identification h x).val = x.val := by
  subst V
  rfl

theorem identification_tangent (D : SliceData F U) (h : U = V)
    (x : D.Point) (v : TangentSpace (𝓡 n) x) :
    (show SpacetimeModelVector n from
      ((D.transport h).tangentEquiv (D.identification h x)
        (mfderiv (𝓡 n) (𝓡 n) (D.identification h) x v)).val) =
      (D.tangentEquiv x v).val := by
  subst V
  change (D.tangentEquiv x (mfderiv (𝓡 n) (𝓡 n) (@id D.Point) x v)).val = _
  rw [mfderiv_id]
  rfl

theorem identification_metric (D : SliceData F U) (h : U = V)
    (x : D.Point) (v w : TangentSpace (𝓡 n) x) :
    (D.transport h).metricOnPoints.inner (D.identification h x)
      (mfderiv (𝓡 n) (𝓡 n) (D.identification h) x v)
      (mfderiv (𝓡 n) (𝓡 n) (D.identification h) x w) =
        D.metricOnPoints.inner x v w := by
  subst V
  change D.metricOnPoints.inner x
    (mfderiv (𝓡 n) (𝓡 n) (@id D.Point) x v)
    (mfderiv (𝓡 n) (𝓡 n) (@id D.Point) x w) = _
  rw [mfderiv_id]
  rfl

noncomputable def toSliceGeometry {t : ℝ}
    (D : SliceData F {p | F.timeFunction p = t}) : SpacetimeSliceGeometry F t where
  chartedSpace := D.chartedSpace
  isManifold := D.isManifold
  t3Space := D.t3Space
  secondCountable := D.secondCountable
  measurableSpace := D.measurableSpace
  borelSpace := D.borelSpace
  inclusion_smooth := D.inclusion_smooth
  inclusion_embedding := D.inclusion_embedding
  inclusion_differential_injective := D.inclusion_differential_injective
  tangentEquiv := D.tangentEquiv
  tangentEquiv_eq := D.tangentEquiv_eq
  metric := D.metric
  metric_eq := D.metric_eq

end SliceData

variable {F : GeneralizedFlowSpacetime n X time I}

noncomputable def sliceTimeIdentification (S : ∀ t, SpacetimeSliceGeometry F t)
    {t t' : ℝ} (h : t = t') : Diffeomorph (𝓡 n) (𝓡 n) (S t).Point (S t').Point ∞ := by
  subst t'
  exact Diffeomorph.refl (𝓡 n) (S t).Point ∞

theorem sliceTimeIdentification_val (S : ∀ t, SpacetimeSliceGeometry F t)
    {t t' : ℝ} (h : t = t') (x : (S t).Point) :
    (sliceTimeIdentification S h x).val = x.val := by
  subst t'
  rfl

theorem sliceTimeIdentification_tangent (S : ∀ t, SpacetimeSliceGeometry F t)
    {t t' : ℝ} (h : t = t') (x : (S t).Point) (v : TangentSpace (𝓡 n) x) :
    (show SpacetimeModelVector n from
      ((S t').tangentEquiv (sliceTimeIdentification S h x)
        (mfderiv (𝓡 n) (𝓡 n) (sliceTimeIdentification S h) x v)).val) =
      ((S t).tangentEquiv x v).val := by
  subst t'
  change ((S t).tangentEquiv x (mfderiv (𝓡 n) (𝓡 n) (@id (S t).Point) x v)).val = _
  rw [mfderiv_id]
  rfl

theorem sliceTimeIdentification_metric (S : ∀ t, SpacetimeSliceGeometry F t)
    {t t' : ℝ} (h : t = t') (x : (S t).Point) (v w : TangentSpace (𝓡 n) x) :
    (S t').metricOnPoints.inner (sliceTimeIdentification S h x)
      (mfderiv (𝓡 n) (𝓡 n) (sliceTimeIdentification S h) x v)
      (mfderiv (𝓡 n) (𝓡 n) (sliceTimeIdentification S h) x w) =
        (S t).metricOnPoints.inner x v w := by
  subst t'
  change (S t).metricOnPoints.inner x
    (mfderiv (𝓡 n) (𝓡 n) (@id (S t).Point) x v)
    (mfderiv (𝓡 n) (𝓡 n) (@id (S t).Point) x w) = _
  rw [mfderiv_id]
  rfl

end PoincareConjecture.M13

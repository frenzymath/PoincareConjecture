import PoincareConjecture.Definitions.Ch19.RampEstimates
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Diffeomorph












set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

def OpenTime (a b : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo a b, isOpen_Ioo⟩

abbrev SpacetimeCarrier (M : Type u) (a b : ℝ) := M × OpenTime a b

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



structure SpacetimeCharts (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (a b : ℝ) where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1)))
    (SpacetimeCarrier M a b)
  isManifold : IsManifold (𝓡 (n + 1)) ∞ (SpacetimeCarrier M a b)
  from_product_smooth : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞
    (id : SpacetimeCarrier M a b → SpacetimeCarrier M a b)
  to_product_smooth : ContMDiff (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
    (id : SpacetimeCarrier M a b → SpacetimeCarrier M a b)
  split : ∀ q : SpacetimeCarrier M a b,
    TangentSpace (𝓡 (n + 1)) q ≃L[ℝ] TangentSpace (𝓡 n) q.1 × ℝ
  split_space : ∀ q V,
    (split q V).1 = mfderiv (𝓡 (n + 1)) (𝓡 n)
      (Prod.fst : SpacetimeCarrier M a b → M) q V
  split_time : ∀ q V,
    (split q V).2 = mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ)
      (fun p : SpacetimeCarrier M a b => (p.2 : ℝ)) q V

namespace SpacetimeCharts

abbrev Point (_C : SpacetimeCharts n M a b) := SpacetimeCarrier M a b

instance (C : SpacetimeCharts n M a b) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) C.Point := C.chartedSpace

instance (C : SpacetimeCharts n M a b) :
    IsManifold (𝓡 (n + 1)) ∞ C.Point := C.isManifold

noncomputable def horizontal (C : SpacetimeCharts n M a b) (q : C.Point)
    (V : TangentSpace (𝓡 n) q.1) : TangentSpace (𝓡 (n + 1)) q :=
  (C.split q).symm (V, 0)

noncomputable def timeVector (C : SpacetimeCharts n M a b) (q : C.Point) :
    TangentSpace (𝓡 (n + 1)) q := (C.split q).symm (0, 1)

noncomputable def liftSpatialField (C : SpacetimeCharts n M a b)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p) (q : C.Point) :
    TangentSpace (𝓡 (n + 1)) q := C.horizontal q (B q.2 q.1)

def IsSmoothField (C : SpacetimeCharts n M a b)
    (V : (q : C.Point) → TangentSpace (𝓡 (n + 1)) q) : Prop :=
  ContMDiff (𝓡 (n + 1))
    ((𝓡 (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) ∞
    (fun q : C.Point => (⟨q, V q⟩ : TangentBundle (𝓡 (n + 1)) C.Point))

end SpacetimeCharts


structure SpacetimeData (F : RicciFlow n M (Set.Icc a b)) where
  charts : SpacetimeCharts n M a b
  metric : RiemannianMetric (n + 1) charts.Point
  connection : LeviCivitaData metric
  metric_eq : ∀ (q : charts.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
    metric.inner q V W =
      (F.metric q.2).inner q.1 (charts.split q V).1 (charts.split q W).1 +
        (charts.split q V).2 * (charts.split q W).2



noncomputable def fixedPointTimeDerivative
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p) (p : M) (t : ℝ) :
    TangentSpace (𝓡 n) p :=
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) p
  e.symmL ℝ p (deriv (fun r => (e ⟨p, B r p⟩).2) t)

namespace SpacetimeData

variable {F : RicciFlow n M (Set.Icc a b)}


noncomputable def covariantAlong (G : SpacetimeData F)
    (gamma : ℝ → G.charts.Point)
    (Y : (s : ℝ) → TangentSpace (𝓡 (n + 1)) (gamma s)) (s : ℝ) :
    TangentSpace (𝓡 (n + 1)) (gamma s) :=
  rampHorizontalCovariantDerivative G.connection gamma Y s


def liftCurve (G : SpacetimeData F) (c : ℝ → ℝ → M) :
    ℝ × OpenTime a b → G.charts.Point := fun z => (c z.1 z.2, z.2)


noncomputable def liftedTimeVelocity (G : SpacetimeData F)
    (c : ℝ → ℝ → M) (z : ℝ × OpenTime a b) :
    TangentSpace (𝓡 (n + 1)) (G.liftCurve c z) :=
  mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1))
    (G.liftCurve c) z (0, 1)

end SpacetimeData



structure CircleGeometry (circumference : ℝ) where
  positive : 0 < circumference
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle circumference)
  isManifold : IsManifold (𝓡 1) ∞ (AddCircle circumference)
  quotient_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
    (fun s : ℝ => (s : AddCircle circumference))
  quotient_local_diffeomorph : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞
    (fun s : ℝ => (s : AddCircle circumference))
  metric : RiemannianMetric 1 (AddCircle circumference)
  connection : LeviCivitaData metric
  metric_quotient : ∀ (s v w : ℝ),
    metric.inner (s : AddCircle circumference)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle circumference)) s v)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle circumference)) s w) = v * w
  frame : ∀ q : AddCircle circumference, TangentSpace (𝓡 1) q
  frame_quotient : ∀ s : ℝ,
    frame (s : AddCircle circumference) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle circumference)) s 1

namespace CircleGeometry

variable {circumference : ℝ}

abbrev Point (_C : CircleGeometry circumference) := AddCircle circumference

instance (C : CircleGeometry circumference) :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) C.Point := C.chartedSpace

instance (C : CircleGeometry circumference) : IsManifold (𝓡 1) ∞ C.Point := C.isManifold

def quotient (C : CircleGeometry circumference) : ℝ → C.Point := fun s => (s : AddCircle _)

abbrev metricOnPoints (C : CircleGeometry circumference) : RiemannianMetric 1 C.Point := C.metric

abbrev connectionOnPoints (C : CircleGeometry circumference) : LeviCivitaData C.metricOnPoints :=
  C.connection

end CircleGeometry


structure CircleProductCharts {circumference : ℝ} (C : CircleGeometry circumference)
    (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (M × C.Point)
  isManifold : IsManifold (𝓡 (n + 1)) ∞ (M × C.Point)
  from_product_smooth : ContMDiff ((𝓡 n).prod (𝓡 1)) (𝓡 (n + 1)) ∞
    (id : M × C.Point → M × C.Point)
  to_product_smooth : ContMDiff (𝓡 (n + 1)) ((𝓡 n).prod (𝓡 1)) ∞
    (id : M × C.Point → M × C.Point)
  split : ∀ q : M × C.Point, TangentSpace (𝓡 (n + 1)) q ≃L[ℝ]
    TangentSpace (𝓡 n) q.1 × TangentSpace (𝓡 1) q.2
  split_space : ∀ q V,
    (split q V).1 = mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : M × C.Point → M) q V
  split_circle : ∀ q V,
    (split q V).2 = mfderiv (𝓡 (n + 1)) (𝓡 1) (Prod.snd : M × C.Point → C.Point) q V

namespace CircleProductCharts

variable {circumference : ℝ} {C : CircleGeometry circumference}

abbrev Point (_P : CircleProductCharts C n M) := M × C.Point

instance (P : CircleProductCharts C n M) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) P.Point := P.chartedSpace

instance (P : CircleProductCharts C n M) : IsManifold (𝓡 (n + 1)) ∞ P.Point := P.isManifold


noncomputable def circleUnit (P : CircleProductCharts C n M) (q : P.Point) :
    TangentSpace (𝓡 (n + 1)) q := (P.split q).symm (0, C.frame q.2)

end CircleProductCharts


structure CircleProductData (F : RicciFlow n M (Set.Icc a b)) (circumference : ℝ) where
  circle : CircleGeometry circumference
  charts : CircleProductCharts circle n M
  flow : RicciFlow (n + 1) charts.Point (Set.Icc a b)
  metric_eq : ∀ (t : ℝ) (q : charts.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
    (flow.metric t).inner q V W =
      (F.metric t).inner q.1 (charts.split q V).1 (charts.split q W).1 +
        circle.metricOnPoints.inner q.2 (charts.split q V).2 (charts.split q W).2

end PoincareConjecture.M62

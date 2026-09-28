import PoincareConjecture.Definitions.M63Polygon
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture



structure M63ProfileProperties (N : ℕ) : Prop where
  normalization_positive :
    0 < ∫ x in (0 : ℝ)..m63CellLength N, m63ProfileBase N x
  smooth : ContDiff ℝ ∞ (m63Profile N)
  periodic : Function.Periodic (m63Profile N) (m63CellLength N)
  nonnegative : ∀ x, 0 ≤ m63Profile N x
  positive : ∀ x ∈ Set.Ioo 0 (m63CellLength N), 0 < m63Profile N x
  symmetric : ∀ x, m63Profile N (m63CellLength N - x) = m63Profile N x
  monotone_half : MonotoneOn (m63Profile N) (Set.Icc 0 (m63CellLength N / 2))
  flat : ∀ (i : ℕ) (j : ℤ),
    iteratedDeriv i (m63Profile N) ((j : ℝ) * m63CellLength N) = 0
  cell_integral : (∫ x in (0 : ℝ)..m63CellLength N, m63Profile N x) =
    m63CellLength N
  flattening_smooth : ContDiff ℝ ∞ (m63Flattening N)
  flattening_derivative : ∀ x, HasDerivAt (m63Flattening N) (m63Profile N x) x
  flattening_strictMono : StrictMono (m63Flattening N)
  flattening_zero : m63Flattening N 0 = 0
  flattening_cell_shift : ∀ x,
    m63Flattening N (x + m63CellLength N) = m63Flattening N x + m63CellLength N
  flattening_period_shift : ∀ x,
    m63Flattening N (x + curvePeriod) = m63Flattening N x + curvePeriod
  circle_homeomorph : ∃ e : AddCircle curvePeriod ≃ₜ AddCircle curvePeriod,
    ∀ x : ℝ, e (x : AddCircle curvePeriod) = (m63Flattening N x : AddCircle curvePeriod)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




structure M63PolygonEstimates {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (t : ℝ) (N : ℕ)
    (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N) : Prop where
  flattened_periodic : Function.Periodic (m63FlattenedPolygon polygon) curvePeriod
  flattened_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (m63FlattenedPolygon polygon)
  flattened_length : m62Length F (fun x _ => m63FlattenedPolygon polygon x) t =
    ∑ j : Fin N, m63CellLength N * (polygon.side j).speed
  flattened_cell_velocity : ∀ (j : Fin N) s, s ∈ Set.Icc 0 (m63CellLength N) →
    let x := m63CellLeft N j + s
    let y := m63Flattening N x - m63CellLeft N j
    m63AngularFirstJet (m63FlattenedPolygon polygon) x =
      (⟨(polygon.side j).map y,
        m63Profile N x • curveVelocity (n := n) (polygon.side j).map y⟩ :
          TangentBundle (𝓡 n) M)
  flattened_cell_speed : ∀ (j : Fin N) s, s ∈ Set.Icc 0 (m63CellLength N) →
    let x := m63CellLeft N j + s
    (F.metric t).tangentNorm (m63FlattenedPolygon polygon x)
      (curveVelocity (n := n) (m63FlattenedPolygon polygon) x) =
        (polygon.side j).speed * m63Profile N x
  graph_periodic : Function.Periodic
    (m63CanonicalRamp P (m63FlattenedPolygon polygon)) curvePeriod
  graph_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞
    (m63CanonicalRamp P (m63FlattenedPolygon polygon))
  graph_ramp : M63IsRampAt P (m63CanonicalRamp P (m63FlattenedPolygon polygon)) t
  graph_velocity : ∀ x,
    let gamma := m63CanonicalRamp P (m63FlattenedPolygon polygon)
    P.charts.split (gamma x) (curveVelocity (n := n + 1) gamma x) =
      (curveVelocity (n := n) (m63FlattenedPolygon polygon) x,
        (circumference / curvePeriod) • P.circle.frame (gamma x).2)
  graph_degree_one :
    ∃ L : M63PositiveDegreeLift P (m63CanonicalRamp P (m63FlattenedPolygon polygon)),
      L.degree = 1
  graph_length :
    m62Length P.flow (fun x _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) x) t ≤
      m62Length F (fun x _ => m63FlattenedPolygon polygon x) t + circumference
  graph_total_curvature : m62TotalCurvature P.flow
    (fun x _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) x) t ≤ (N : ℝ) * Real.pi



def M63SampledPolygonLengthComparison (F : RicciFlow n M (Set.Icc a b)) : Prop :=
  ∀ t ∈ Set.Icc a b, ∀ N : ℕ, 0 < N →
    ∀ polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N,
    ∀ gamma : ℝ → M, Function.Periodic gamma curvePeriod →
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma →
      (∀ j : Fin N, polygon.vertices j = gamma (m63CellLeft N j)) →
        (∑ j : Fin N, m63CellLength N * (polygon.side j).speed) ≤
          m62Length F (fun x _ => gamma x) t

end PoincareConjecture

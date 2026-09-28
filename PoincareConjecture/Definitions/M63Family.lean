import PoincareConjecture.Definitions.M63Polygon
import PoincareConjecture.Definitions.M61Width

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

structure M63RawApproximation (F : RicciFlow 3 M (Set.Icc a b))
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (zeta : ℝ) where
  count : ℕ
  count_positive : 0 < count
  polygon : LoopTwoSphere →
    M63GeodesicPolygon (F.metric a) (F.connection a) count
  sample_eq : ∀ z (j : Fin count),
    (polygon z).vertices j = periodicFreeLoop (Gamma z) (m63CellLeft count j)
  family : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))
  null_family : M61NullFamily family
  homotopic : Gamma.Homotopic family
  angular_eq : ∀ z x,
    periodicFreeLoop (family z) x = m63FlattenedPolygon (polygon z) x
  angular_smooth : ∀ z,
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (periodicFreeLoop (family z))
  first_jet_continuous : Continuous (fun z : LoopTwoSphere × ℝ =>
    m63AngularFirstJet (n := 3) (periodicFreeLoop (family z.1)) z.2)
  second_jet_continuous : Continuous (fun z : LoopTwoSphere × ℝ =>
    m63AngularSecondJet (F.connection a) (periodicFreeLoop (family z.1)) z.2)
  length_loss : ∀ z,
    0 ≤ freeLoopLength (F.metric a) (Gamma z) - freeLoopLength (F.metric a) (family z) ∧
      freeLoopLength (F.metric a) (Gamma z) - freeLoopLength (F.metric a) (family z) < zeta
  area_error : ∀ z,
    |fillingArea (F.metric a) (family z) - fillingArea (F.metric a) (Gamma z)| < zeta

structure M63ProductSolutionFamily
    {F : RicciFlow 3 M (Set.Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    (approximation : M63RawApproximation F Gamma zeta) where
  curve : LoopTwoSphere → ℝ → ℝ → P.charts.Point
  shrinking : ∀ z, M62ShrinkingCurve P.flow (curve z)
  intrinsic_regular : ∀ z,
    M63IntrinsicRegularityOn P.flow (curve z) (Set.Icc a b)
  initial_eq : ∀ z x,
    curve z x a = m63CanonicalRamp P (periodicFreeLoop (approximation.family z)) x
  ramp : ∀ z t, t ∈ Set.Icc a b → M63IsRampAt P (fun x => curve z x t) t
  degree_one : ∀ z t, t ∈ Set.Icc a b →
    ∃ lift : M63PositiveDegreeLift P (fun x => curve z x t), lift.degree = 1
  value_continuous : Continuous (fun p : LoopTwoSphere × ℝ × Set.Icc a b =>
    curve p.1 p.2.1 p.2.2.1)
  velocity_continuous : Continuous (fun p : LoopTwoSphere × ℝ × Set.Icc a b =>
    m63AngularFirstJet (n := 3 + 1) (fun x => curve p.1 x p.2.2.1) p.2.1)
  projected : Set.Icc a b → ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))
  projected_continuous : Continuous (fun p : Set.Icc a b × LoopTwoSphere =>
    projected p.1 p.2)
  projected_eq : ∀ (t : Set.Icc a b) z x,
    periodicFreeLoop (projected t z) x = (curve z x t.1).1
  projected_initial : ∀ ha : a ∈ Set.Icc a b,
    projected ⟨a, ha⟩ = approximation.family
  projected_null : ∀ t, M61NullFamily (projected t)

end PoincareConjecture

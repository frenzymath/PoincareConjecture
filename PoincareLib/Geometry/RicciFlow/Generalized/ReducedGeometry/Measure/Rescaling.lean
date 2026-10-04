import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Analytic

/-! Adapted from Mapher `PoincareMT/Statements/M14GeneralizedLGeometry.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- Analytic transport for a prescribed positive M13 rescaling. The target
clock, interval and primitive geometric identities are part of the type. -/
structure M14AnalyticRescalingData
    (G : GeneralizedLGeometryTransport n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (G' : GeneralizedLGeometryTransport n X
      (fun x => parabolicTime Q a (time x)) (parabolicInterval Q hQ a I)) where
  chartedSpace_eq : G'.spacetime.chartedSpace = G.spacetime.chartedSpace
  point_equiv : Diffeomorph (spacetimeModel n) (spacetimeModel n) G.Point G'.Point ∞
  point_equiv_eq : ∀ p, point_equiv p = p
  point_differential : ∀ p (Z : TangentSpace (spacetimeModel n) p),
    (show SpacetimeModelVector n from
      mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p Z) = Z
  point_time : ∀ p,
    G'.spacetime.timeFunction (point_equiv p) =
      parabolicTime Q a (G.spacetime.timeFunction p)
  timeVector_map : ∀ p,
    mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p
      (G.spacetime.timeVector p) = Q • G'.spacetime.timeVector (point_equiv p)
  horizontal_map : ∀ p, G.Horizontal p ≃L[ℝ] G'.Horizontal (point_equiv p)
  horizontal_differential : ∀ p (v : G.Horizontal p),
    (horizontal_map p v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p v.val
  horizontal_metric : ∀ p v w,
    G'.spacetime.horizontalMetric.inner (point_equiv p)
      (horizontal_map p v) (horizontal_map p w) =
      Q * G.spacetime.horizontalMetric.inner p v w
  scalar_curvature : ∀ p,
    horizontalScalarCurvature G'.leafwise (point_equiv p) =
      Q⁻¹ * horizontalScalarCurvature G.leafwise p
  slice_identification : ∀ t,
    Diffeomorph (𝓡 n) (𝓡 n) (G.slices t).Point
      (G'.slices (parabolicTime Q a t)).Point ∞
  slice_identification_eq : ∀ t x,
    (slice_identification t x).val = point_equiv x.val
  slice_tangent : ∀ t (x : (G.slices t).Point) (v : TangentSpace (𝓡 n) x),
    (show SpacetimeModelVector n from
      ((G'.slices (parabolicTime Q a t)).tangentEquiv (slice_identification t x)
        (mfderiv (𝓡 n) (𝓡 n) (slice_identification t) x v)).val) =
      (horizontal_map x.val ((G.slices t).tangentEquiv x v)).val
  slice_metric : ∀ t,
    MetricHomothety (G.slices t).metricOnPoints
      (G'.slices (parabolicTime Q a t)).metricOnPoints (slice_identification t) Q
  initial_equiv : ∀ x : G.Point,
    G.Horizontal x ≃L[ℝ] G'.Horizontal (point_equiv x)
  initial_equiv_eq : ∀ x v,
    initial_equiv x v = (Real.sqrt Q)⁻¹ • horizontal_map x v
  initial_equiv_isometry : ∀ x v w,
    G'.spacetime.horizontalMetric.inner (point_equiv x)
      (initial_equiv x v) (initial_equiv x w) =
      G.spacetime.horizontalMetric.inner x v w
  path_map : ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point),
    M14BackwardPath G T τ₁ τ₂ x y →
    M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)
  path_map_eq : ∀ T τ₁ τ₂ x y p s,
    (path_map T τ₁ τ₂ x y p).curve (Q * s) = point_equiv (p.curve s)
  action_scale : ∀ T τ₁ τ₂ x y p,
    M14BackwardLAction G' (path_map T τ₁ τ₂ x y p) =
      Real.sqrt Q * M14BackwardLAction G p
  path_inverse : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      ∀ s, p'.curve (Q * s) = point_equiv (p.curve s)
  path_inverse_exact : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      path_map T τ₁ τ₂ x y p = p'
  path_minimizer_iff : ∀ T τ₁ τ₂ x y
    (p : M14BackwardPath G T τ₁ τ₂ x y),
    M14IsMinimizing (path_map T τ₁ τ₂ x y p) ↔ M14IsMinimizing p
  path_inverse_action : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      path_map T τ₁ τ₂ x y p = p' ∧
      M14BackwardLAction G' p' =
        Real.sqrt Q * M14BackwardLAction G p
  reduced_length_scale : ∀ T τ₁ τ₂ x y,
    0 < τ₂ → M14FiniteValueDomain G T τ₁ τ₂ x y →
    M14ReducedLengthValue G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
        (point_equiv x) (point_equiv y) =
      M14ReducedLengthValue G T τ₁ τ₂ x y
  density : ∀ (_T _τ : ℝ) (_x _q : G.Point), ℝ
  density_eq : ∀ T τ x q,
    0 < τ → G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G T 0 τ x q →
    density T τ x q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q)
  density' : ∀ (_T _τ : ℝ) (_x _q : G'.Point), ℝ
  density'_eq : ∀ T τ x q,
    0 < τ → G'.spacetime.timeFunction x = T →
    G'.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G' T 0 τ x q →
    density' T τ x q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G' T 0 τ x q)
  density_scale : ∀ T τ x q,
    0 < τ → G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G T 0 τ x q →
    density' (parabolicTime Q a T) (Q * τ) (point_equiv x) (point_equiv q) =
      Real.rpow Q (-(n : ℝ) / 2) * density T τ x q
  target_family : ∀ (T : ℝ) (x : G.Point) (_E : M14ExponentialFamily G T x),
    M14ExponentialFamily G' (parabolicTime Q a T) (point_equiv x)
  exponential_domain_transport : ∀ T x (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ E.domain ↔
      (initial_equiv x Z, Real.sqrt Q * s) ∈ (target_family T x E).domain
  exponential_transport : ∀ T x (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ E.domain →
      (target_family T x E).gamma (initial_equiv x Z) (Real.sqrt Q * s) =
        point_equiv (E.gamma Z s)
  stable_transport : ∀ (T τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
      ∃ H' : M14StableSet G' (parabolicTime Q a T) (Q * τ)
          (point_equiv x) (target_family T x E),
        (∀ Z, Z ∈ H.carrier ↔ initial_equiv x Z ∈ H'.carrier) ∧
        ∃ D : M14MeasureJacobianData G T τ x E H,
          ∃ D' : M14MeasureJacobianData G' (parabolicTime Q a T) (Q * τ)
              (point_equiv x) (target_family T x E) H',
            (∀ Z, Z ∈ H.carrier →
              D'.jacobian (initial_equiv x Z) =
                Real.rpow Q ((n : ℝ) / 2) * D.jacobian Z) ∧
            (fun q => point_equiv q.val) ''
                (H.endpoint_slice_map '' H.carrier) =
              (fun q => q.val) '' (H'.endpoint_slice_map '' H'.carrier) ∧
            (∫ q in H.endpoint_slice_map '' H.carrier,
                density T τ x q.val ∂calibratedMetricVolume
                  (G.slices (T - τ)).metricOnPoints) =
              ∫ q' in H'.endpoint_slice_map '' H'.carrier,
                density' (parabolicTime Q a T) (Q * τ) (point_equiv x) q'.val
                  ∂calibratedMetricVolume
                    (G'.slices (parabolicTime Q a T - Q * τ)).metricOnPoints
  joint_domain_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ M14JointDomain G E ↔
      (initial_equiv x Z, Real.sqrt Q * s) ∈
        M14JointDomain G' (target_family T x E)
  jacobian_data : ∀ (T τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    Nonempty (M14MeasureJacobianData G T τ x E H)

def M14AnalyticRescalingConclusion
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    ∃ G' : GeneralizedLGeometryTransport n X
      (fun x => parabolicTime Q a (time x)) (parabolicInterval Q hQ a I),
      Nonempty (M14AnalyticRescalingData G Q hQ a G')


end PoincareMT

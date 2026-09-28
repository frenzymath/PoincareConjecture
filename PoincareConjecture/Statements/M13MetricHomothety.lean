import PoincareConjecture.Definitions.M13MetricHomothety
import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Definitions.Ch06.ReducedVolume












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [T3Space N] [MeasurableSpace N] [BorelSpace N]




structure MetricHomothetyCalculus (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (Q : ℝ) : Prop where
  tangent_norm : ∀ (x : M) (u : TangentSpace (𝓡 n) x),
    h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) =
      Real.sqrt Q * g.tangentNorm x u
  tangent_norm_sq : ∀ (x : M) (u : TangentSpace (𝓡 n) x),
    (h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)) ^ 2 =
      Q * (g.tangentNorm x u) ^ 2
  path_length : ∀ (a b : ℝ), a ≤ b → ∀ γ : ℝ → M,
    ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Set.Icc a b) →
      h.pathELength (f ∘ γ) a b = ENNReal.ofReal (Real.sqrt Q) * g.pathELength γ a b
  edist_eq : ∀ x y : M,
    h.edist (f x) (f y) = ENNReal.ofReal (Real.sqrt Q) * g.edist x y
  ball_image : ∀ (x : M) (r : ℝ),
    f '' g.ball x r = h.ball (f x) (Real.sqrt Q * r)
  complete_iff : MetricComplete h ↔ MetricComplete g
  compact_image_iff : ∀ E : Set M, IsCompact (f '' E) ↔ IsCompact E
  volume_map : calibratedMetricVolume h =
    ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) •
      MeasureTheory.Measure.map f (calibratedMetricVolume g)
  volume_image : ∀ E : Set M,
    calibratedMetricVolume h (f '' E) =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * calibratedMetricVolume g E
  connection_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (U : Set M), IsOpen U →
    ∀ (V : (x : M) → TangentSpace (𝓡 n) x)
      (W : (y : N) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) (f '' U) →
      (∀ x ∈ U, W (f x) = mfderiv (𝓡 n) (𝓡 n) f x (V x)) →
      ∀ x ∈ U, ∀ u : TangentSpace (𝓡 n) x,
        D'.connection W (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) =
          mfderiv (𝓡 n) (𝓡 n) f x (D.connection V x u)
  curvature_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v w : TangentSpace (𝓡 n) x),
    D'.curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) =
        mfderiv (𝓡 n) (𝓡 n) f x (D.curvature x u v w)
  riemann_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v w z : TangentSpace (𝓡 n) x),
    D'.curvatureTensor (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
      (mfderiv (𝓡 n) (𝓡 n) f x z) = Q * D.curvatureTensor x u v w z
  ricci_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v : TangentSpace (𝓡 n) x),
    D'.ricci (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      D.ricci x u v
  scalar_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M),
    D'.scalarCurvature (f x) = D.scalarCurvature x / Q
  sectional_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v : TangentSpace (𝓡 n) x),
    D'.sectionalCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) = D.sectionalCurvature x u v / Q
  curvature_norm_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M),
    D'.curvatureTensorNorm (f x) = D.curvatureTensorNorm x / Q
  curvature_norm_sq_eq : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M),
    (D'.curvatureTensorNorm (f x)) ^ 2 = (D.curvatureTensorNorm x) ^ 2 / Q ^ 2
  curvature_bound_iff : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (E : Set M) (K : ℝ),
    (∀ y ∈ f '' E, D'.curvatureTensorNorm y ≤ K / Q) ↔
      ∀ x ∈ E, D.curvatureTensorNorm x ≤ K
  nonnegative_operator_iff : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M),
    D'.NonnegativeCurvatureOperator (f x) ↔ D.NonnegativeCurvatureOperator x
  operator_bound_iff : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h) (K : ℝ) (x : M),
    D'.CurvatureOperatorBound (K / Q) (f x) ↔ D.CurvatureOperatorBound K x
  nonflat_iff : ∀ (D : LeviCivitaData g) (D' : LeviCivitaData h),
    (∃ y : N, D'.curvatureTensorNorm y ≠ 0) ↔ ∃ x : M, D.curvatureTensorNorm x ≠ 0

end PoincareConjecture

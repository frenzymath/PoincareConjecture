import PoincareConjecture.Definitions.M62Geometry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



structure SpacetimeIdentities {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) : Prop where
  time_smooth : G.charts.IsSmoothField G.charts.timeVector
  time_unit : ∀ q, G.metric.inner q (G.charts.timeVector q) (G.charts.timeVector q) = 1
  time_parallel_time : ∀ q,
    G.connection.connection G.charts.timeVector q (G.charts.timeVector q) = 0
  spatial_connection : ∀ (B : ℝ → (p : M) → TangentSpace (𝓡 n) p),
    G.charts.IsSmoothField (G.charts.liftSpatialField B) →
    ∀ (q : G.charts.Point) (V : TangentSpace (𝓡 n) q.1),
      G.charts.split q
          (G.connection.connection (G.charts.liftSpatialField B) q
            (G.charts.horizontal q V)) =
        ((F.connection q.2).connection (B q.2) q.1 V,
          (F.connection q.2).ricci q.1 V (B q.2 q.1))
  spatial_time_vertical : ∀ (q : G.charts.Point) (V : TangentSpace (𝓡 n) q.1),
    (G.charts.split q (G.connection.connection G.charts.timeVector q
      (G.charts.horizontal q V))).2 = 0
  spatial_time_pairing : ∀ (q : G.charts.Point) (V W : TangentSpace (𝓡 n) q.1),
    G.metric.inner q
      (G.connection.connection G.charts.timeVector q (G.charts.horizontal q V))
      (G.charts.horizontal q W) = -(F.connection q.2).ricci q.1 V W
  time_spatial_vertical : ∀ (B : ℝ → (p : M) → TangentSpace (𝓡 n) p),
    G.charts.IsSmoothField (G.charts.liftSpatialField B) → ∀ q,
      (G.charts.split q (G.connection.connection (G.charts.liftSpatialField B)
        q (G.charts.timeVector q))).2 = 0
  time_spatial_pairing : ∀ (B : ℝ → (p : M) → TangentSpace (𝓡 n) p),
    G.charts.IsSmoothField (G.charts.liftSpatialField B) →
    ∀ (q : G.charts.Point) (W : TangentSpace (𝓡 n) q.1),
      G.metric.inner q
        (G.connection.connection (G.charts.liftSpatialField B) q (G.charts.timeVector q))
        (G.charts.horizontal q W) =
      (F.metric q.2).inner q.1 (fixedPointTimeDerivative B q.1 q.2) W -
        (F.connection q.2).ricci q.1 (B q.2 q.1) W
  gauss : ∀ (q : G.charts.Point) (A B C D : TangentSpace (𝓡 n) q.1),
    G.connection.curvatureTensor q
        (G.charts.horizontal q A) (G.charts.horizontal q B)
        (G.charts.horizontal q C) (G.charts.horizontal q D) =
      (F.connection q.2).curvatureTensor q.1 A B C D -
        (F.connection q.2).ricci q.1 B D * (F.connection q.2).ricci q.1 A C +
        (F.connection q.2).ricci q.1 A D * (F.connection q.2).ricci q.1 B C
  codazzi : ∀ (q : G.charts.Point) (B C D : TangentSpace (𝓡 n) q.1),
    G.connection.curvatureTensor q (G.charts.timeVector q)
        (G.charts.horizontal q B) (G.charts.horizontal q C) (G.charts.horizontal q D) =
      (F.connection q.2).covariantTensorDerivative (F.connection q.2).ricciEvaluation
          q.1 ![C, B, D] -
        (F.connection q.2).covariantTensorDerivative (F.connection q.2).ricciEvaluation
          q.1 ![D, B, C]

structure CircleIdentities {circumference : ℝ} (C : CircleGeometry circumference) : Prop where
  frame_smooth : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
    (fun q : C.Point => (⟨q, C.frame q⟩ : TangentBundle (𝓡 1) C.Point))
  frame_unit : ∀ q : C.Point, C.metricOnPoints.inner q (C.frame q) (C.frame q) = 1
  frame_parallel : ∀ (q : C.Point) (V : TangentSpace (𝓡 1) q),
    C.connectionOnPoints.connection C.frame q V = 0
  curvature_zero : ∀ (q : C.Point) (V W Z T : TangentSpace (𝓡 1) q),
    C.connectionOnPoints.curvatureTensor q V W Z T = 0
  circumference_eq :
    C.metricOnPoints.pathELength C.quotient 0 circumference = ENNReal.ofReal circumference



structure CircleProductIdentities {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : CircleProductData F circumference) : Prop where
  circle_identities : CircleIdentities P.circle
  circle_unit_smooth : ContMDiff (𝓡 (n + 1))
    ((𝓡 (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) ∞
    (fun q : P.charts.Point =>
      (⟨q, P.charts.circleUnit q⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point))
  circle_unit : ∀ (t : ℝ) (q : P.charts.Point),
    (P.flow.metric t).inner q (P.charts.circleUnit q) (P.charts.circleUnit q) = 1
  circle_parallel : ∀ (t : ℝ) (q : P.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q),
    (P.flow.connection t).connection P.charts.circleUnit q V = 0
  circle_ricci : ∀ (t : ℝ) (q : P.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q),
    (P.flow.connection t).ricci q V (P.charts.circleUnit q) = 0
  riemann_split : ∀ (t : ℝ) (q : P.charts.Point)
    (V W Z T : TangentSpace (𝓡 (n + 1)) q),
    (P.flow.connection t).curvatureTensor q V W Z T =
      (F.connection t).curvatureTensor q.1 (P.charts.split q V).1
        (P.charts.split q W).1 (P.charts.split q Z).1 (P.charts.split q T).1
  ricci_split : ∀ (t : ℝ) (q : P.charts.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
    (P.flow.connection t).ricci q V W =
      (F.connection t).ricci q.1 (P.charts.split q V).1 (P.charts.split q W).1
  ricci_derivative_split : ∀ (t : ℝ) (q : P.charts.Point)
    (A V W : TangentSpace (𝓡 (n + 1)) q),
    (P.flow.connection t).covariantTensorDerivative (P.flow.connection t).ricciEvaluation
      q ![A, V, W] =
    (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
      q.1 ![(P.charts.split q A).1, (P.charts.split q V).1, (P.charts.split q W).1]


def CircleUnitSpacetimeParallel {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : CircleProductData F circumference)
    (G : SpacetimeData P.flow) : Prop :=
  ∀ (q : G.charts.Point) (V : TangentSpace (𝓡 (n + 1 + 1)) q),
    G.connection.connection
      (G.charts.liftSpatialField (fun _ => P.charts.circleUnit)) q V = 0

end PoincareConjecture.M62

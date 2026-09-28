import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FlowConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric

set_option autoImplicit false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff
open PoincareConjecture.ChartDistance

universe u

namespace PoincareConjecture.M30

structure PartialLimitWindowExport
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {tau : ℝ}
    (F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0))
    (p : ∀ k, M k) (A : ℝ) where
  tau_pos : 0 < tau
  limit : PartialPointedFlowConvergence F p A 0

def PartialLimitWindowExport.embedding
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A : ℝ}
    (E : PartialLimitWindowExport F p A) :
    ∀ k, E.limit.limitCarrier.carrier → M (E.limit.subsequence k) :=
  E.limit.embedding

structure SelectedParabolicApplicationData
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (tau A : ℝ) where
  tau_pos : 0 < tau
  U : ℕ → Set (EuclideanSpace ℝ (Fin 3))
  isOpen_U : ∀ i, IsOpen (U i)
  convex_U : ∀ i, Convex ℝ (U i)
  piece_nonempty : ∀ i, Nonempty (Piece U i)
  embedding : ∀ k i, Piece U i → M k
  distance_limit : ∀ i j, C(Piece U i × Piece U j, ℝ)
  distance_limit_spec : ∀ i j, TendstoLocallyUniformly
    (fun k (p : Piece U i × Piece U j) =>
      dist (embedding k i p.1) (embedding k j p.2))
      (distance_limit i j) atTop
  lipschitz_constant : ℕ → ℝ≥0
  lipschitz : ∀ k i, LipschitzWith (lipschitz_constant i) (embedding k i)
  lower_constant : ℕ → ℝ
  lower_constant_pos : ∀ i, 0 < lower_constant i
  lower_distance : ∀ k i x y,
    lower_constant i * dist x y ≤ dist (embedding k i x) (embedding k i y)
  open_embedding : ∀ k i, Topology.IsOpenEmbedding (embedding k i)
  ball_preconnected : ∀ k (p : M k) r, IsPreconnected (ball p r)
  smooth :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
      fun i => (isOpen_U i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ k i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (embedding k i)
  transition_bounds : ∀ i j, LocallyEventuallyBoundedDerivatives
    (Subtype.val '' overlap (fun i j => distance_limit i j) i j)
    (fun k => coordinateRepresentative (U := U) (hU := isOpen_U)
      (i := i) (j := j)
      (fun x : Piece U i => Function.invFun (embedding k j) (embedding k i x)))
  base_index : ℕ
  base_point : Piece U base_index
  radius_pos : 0 < A
  range_bound : ∀ i (x : Piece U i),
    distance_limit base_index i (base_point, x) < A
  compact_cover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
    ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
      ∀ᶠ k in atTop,
        ball (embedding k base_index base_point) R ⊆
          ⋃ i ∈ s, embedding k i '' K i
  flow : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)
  distance_eq : ∀ k (x y : M k),
    edist x y = ((flow k).metric 0).edist x y
  metric_jets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
    IsCompact K → K ⊆ Icc (-tau) 0 ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m
          (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((flow k).metric w.1).pullbackCoefficients
              (chartParametrization (U := U) (hU := isOpen_U) (i := i)
                (embedding k i)) w.2)
          (Icc (-tau) 0 ×ˢ U i) z‖ ≤ C
  positive_ellipticity : ∀ t ∈ Icc (-tau) 0, ∀ i x, x ∈ U i →
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ v,
      a * ‖v‖ ^ 2 ≤
        ((flow k).metric t).pullbackCoefficients
          (chartParametrization (U := U) (hU := isOpen_U) (i := i)
            (embedding k i)) x v v

def PartialLimitWindowService : Prop :=
  ∀ (M : ℕ → Type u) [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)],
    ∀ (tau A : ℝ)
      (H : SelectedParabolicApplicationData (M := M) tau A),
      Nonempty (PartialLimitWindowExport H.flow
        (fun k => H.embedding k H.base_index H.base_point) A)

end PoincareConjecture.M30

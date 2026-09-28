import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.M17BlowupSetup













set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]




def ancientM18TimeWindow (j : ℕ) : Set ℝ :=
  Set.Icc (-((j : ℝ) + 1)) (-((j : ℝ) + 1)⁻¹)






structure AncientCompactTimeConvergence {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) where
  limit : AncientLimitFlow n
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : ℕ → Set limit.carrier.carrier
  exhaustion_open : ∀ j,
    letI : TopologicalSpace limit.carrier.carrier := limit.carrier.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j,
    letI : TopologicalSpace limit.carrier.carrier := limit.carrier.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j,
    letI : TopologicalSpace limit.carrier.carrier := limit.carrier.topologicalSpace
    IsCompact (closure (exhaustion j))
  base_in_exhaustion : ∀ j, limit.base ∈ exhaustion j
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  time_window_subset : ∀ j, ancientM18TimeWindow j ⊆ Set.Iio 0
  time_window_increasing : ∀ j,
    ancientM18TimeWindow j ⊆ ancientM18TimeWindow (j + 1)
  time_window_base : ∀ j, (-1 : ℝ) ∈ ancientM18TimeWindow j
  time_window_covers : ⋃ j, ancientM18TimeWindow j = Set.Iio 0
  embedding : ∀ j,
    AncientSpacetimeEmbedding (K := K) (R := S.rescaling (subsequence j)) limit
      (ancientM18TimeWindow j ×ˢ exhaustion j)
  spatial_time_independent : ∀ j (s t : ℝ) (x : limit.carrier.carrier),
    s ∈ ancientM18TimeWindow j → t ∈ ancientM18TimeWindow j → x ∈ exhaustion j →
      ((embedding j).toFun (s, x)).2 = ((embedding j).toFun (t, x)).2
  base_preserving : ∀ j,
    (embedding j).toFun (-1, limit.base) =
      (-1, S.base (subsequence j))
  pullback_metric_CInfinity :
    letI : TopologicalSpace limit.carrier.carrier := limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) limit.carrier.carrier :=
      limit.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ limit.carrier.carrier := limit.carrier.isManifold
    ∀ q : limit.carrier.carrier, ∀ j r : ℕ,
      ∀ Kc : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact Kc →
      Kc ⊆ {p | p.1 ∈ ancientM18TimeWindow j ∧
        p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ p ∈ Kc,
          ‖MetricJet r
              (ancientPullbackCoefficient
                (embedding k) q a b) Kc p -
            MetricJet r
              (FlowCarrier.coordinateCoefficient limit.carrier q
                (fun t x v w ↦ (limit.flow.metric t).inner x v w)
                a b) Kc p‖ < ε






structure AncientAsymptoticSolitonLimitData
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K) where
  convergence : AncientCompactTimeConvergence S
  nonflat_at : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace convergence.limit.carrier.carrier :=
      convergence.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) convergence.limit.carrier.carrier :=
      convergence.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ convergence.limit.carrier.carrier :=
      convergence.limit.carrier.isManifold
    ∃ x : convergence.limit.carrier.carrier,
      (convergence.limit.flow.connection t).curvatureTensorNorm x ≠ 0
  kappa_noncollapsed : AncientLimitKappaNoncollapsed convergence.limit K.kappa
  scalar_curvature_nonnegative_time_derivative :
    ∀ t : ℝ, t < 0 →
      letI : TopologicalSpace convergence.limit.carrier.carrier :=
        convergence.limit.carrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) convergence.limit.carrier.carrier :=
        convergence.limit.carrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ convergence.limit.carrier.carrier :=
        convergence.limit.carrier.isManifold
      ∀ x : convergence.limit.carrier.carrier, ∃ dR : ℝ,
      HasDerivWithinAt
        (fun s ↦ (convergence.limit.flow.connection s).scalarCurvature x) dR
        (Set.Iio 0) t ∧ 0 ≤ dR
  potential : convergence.limit.carrier.carrier × ℝ → ℝ
  potential_smooth :
    letI : TopologicalSpace convergence.limit.carrier.carrier :=
      convergence.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) convergence.limit.carrier.carrier :=
      convergence.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ convergence.limit.carrier.carrier :=
      convergence.limit.carrier.isManifold
    ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ potential
      (Set.univ ×ˢ Set.Iio 0)
  soliton_equation :
    ∀ t : ℝ, t < 0 →
      letI : TopologicalSpace convergence.limit.carrier.carrier :=
        convergence.limit.carrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) convergence.limit.carrier.carrier :=
        convergence.limit.carrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ convergence.limit.carrier.carrier :=
        convergence.limit.carrier.isManifold
      ∀ x : convergence.limit.carrier.carrier,
      ∀ u v : convergence.limit.carrier.tangent x,
        (convergence.limit.flow.connection t).ricci x u v +
            (convergence.limit.flow.connection t).hessian
              (fun y ↦ potential (y, t)) x u v +
            (1 / (2 * t)) *
              (convergence.limit.flow.metric t).inner x u v = 0

end PoincareConjecture

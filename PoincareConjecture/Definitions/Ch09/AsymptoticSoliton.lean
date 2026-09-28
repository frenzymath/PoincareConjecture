import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Definitions.Ch06.ReducedVolume
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.Diffeomorph











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]








def AncientKappaNoncollapsed (F : RicciFlow n M (Set.Iic 0)) (κ : ℝ) : Prop :=
  ∀ r₀ : ℝ, 0 < r₀ →
    ∀ (t : ℝ), t ≤ 0 → ∀ p : M, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r)


structure AncientKappaSolution (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] where
  flow : RicciFlow n M (Set.Iic 0)
  kappa : ℝ
  kappa_pos : 0 < kappa
  complete : ∀ t : ℝ, t ≤ 0 → MetricComplete (flow.metric t)
  nonnegative_curvature_operator :
    ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) x
  bounded_curvature : ∀ t : ℝ, t ≤ 0 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : M, |(flow.connection t).curvatureTensorNorm x| ≤ K
  nonflat : ∀ t : ℝ, t ≤ 0 → ∃ x : M,
    (flow.connection t).curvatureTensorNorm x ≠ 0
  noncollapsed : AncientKappaNoncollapsed flow kappa







structure AncientRescaling (K : AncientKappaSolution n M) (tau : ℝ) where
  tau_pos : 0 < tau
  flow : RicciFlow n M (Set.Iio 0)
  metric_scale : ∀ t : ℝ, t < 0 → ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
    (flow.metric t).inner x v w =
      (1 / tau) * (K.flow.metric (tau * t)).inner x v w
  ricci_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    ∀ v w : TangentSpace (𝓡 n) x,
      (flow.connection t).ricci x v w =
        (K.flow.connection (tau * t)).ricci x v w
  scalar_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    (flow.connection t).scalarCurvature x =
      tau * (K.flow.connection (tau * t)).scalarCurvature x
  curvature_norm_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    (flow.connection t).curvatureTensorNorm x =
      tau * (K.flow.connection (tau * t)).curvatureTensorNorm x


structure AncientRescalingSequence (K : AncientKappaSolution n M) where
  reference : M
  scale : ℕ → ℝ
  scale_pos : ∀ k, 0 < scale k
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  rescaling : ∀ k, AncientRescaling K (scale k)
  base : ℕ → M
  base_minimizing : ∀ k, ∀ y : M,
    reducedLength K.flow 0 reference (base k) (scale k) ≤
      reducedLength K.flow 0 reference y (scale k)
  base_reduced_length_bound : ∀ k,
    reducedLength K.flow 0 reference (base k) (scale k) ≤ (n : ℝ) / 2


structure AncientLimitFlow (n : ℕ) where
  carrier : FlowCarrier n
  base : carrier.carrier
  flow : @RicciFlow n carrier.carrier carrier.topologicalSpace carrier.chartedSpace
    carrier.isManifold (Set.Iio 0)
  complete : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ carrier.carrier := carrier.isManifold
    letI : T3Space carrier.carrier := carrier.t3Space
    @FlowCarrier.metricComplete n carrier (flow.metric t)
  nonnegative_curvature_operator : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ carrier.carrier := carrier.isManifold
    ∀ x : carrier.carrier,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) x


structure AncientSpacetimeEmbedding {K : AncientKappaSolution n M}
    {tau : ℝ} {R : AncientRescaling K tau} (L : AncientLimitFlow n)
    (domain : Set (ℝ × L.carrier.carrier)) where
  toFun : ℝ × L.carrier.carrier → ℝ × M
  time_preserving : ∀ t x, (toFun (t, x)).1 = t
  injective_on : Set.InjOn toFun domain
  inverse : ℝ × M → ℝ × L.carrier.carrier
  left_inverse : ∀ p ∈ domain, inverse (toFun p) = p
  right_inverse : ∀ q ∈ toFun '' domain, toFun (inverse q) = q
  smooth_on :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier :=
      L.carrier.chartedSpace
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      toFun domain
  smooth_inverse_on :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier :=
      L.carrier.chartedSpace
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      inverse (toFun '' domain)


noncomputable def ancientPullbackInnerValue {K : AncientKappaSolution n M}
    {tau : ℝ} {R : AncientRescaling K tau} {L : AncientLimitFlow n}
    {domain : Set (ℝ × L.carrier.carrier)}
    (e : AncientSpacetimeEmbedding (K := K) (R := R) L domain)
    (t : ℝ) (x : L.carrier.carrier)
    (v w : L.carrier.tangent x) : ℝ :=
  letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier :=
    L.carrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
  let ψ : L.carrier.carrier → M := fun y ↦ (e.toFun (t, y)).2
  (R.flow.metric t).inner (ψ x)
    (mfderiv (𝓡 n) (𝓡 n) ψ x v)
    (mfderiv (𝓡 n) (𝓡 n) ψ x w)


noncomputable def ancientPullbackCoefficient {K : AncientKappaSolution n M}
    {tau : ℝ} {R : AncientRescaling K tau} {L : AncientLimitFlow n}
    {domain : Set (ℝ × L.carrier.carrier)}
    (e : AncientSpacetimeEmbedding (K := K) (R := R) L domain)
      (q : L.carrier.carrier)
    (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier :=
    L.carrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
  let c := extChartAt (𝓡 n) q
  let A := mfderiv (𝓡 n) (𝓡 n) c.symm p.2
  ancientPullbackInnerValue e p.1 (c.symm p.2)
    (A (EuclideanSpace.basisFun (Fin n) ℝ a))
    (A (EuclideanSpace.basisFun (Fin n) ℝ b))


structure AncientGeometricConvergence {K : AncientKappaSolution n M}
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
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  embedding : ∀ j,
    AncientSpacetimeEmbedding (K := K) (R := S.rescaling (subsequence j)) limit
      (Set.Iio 0 ×ˢ exhaustion j)
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
      Kc ⊆ {p | p.1 < 0 ∧ p.2 ∈ (extChartAt (𝓡 n) q).target ∧
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


def AncientLimitKappaNoncollapsed (L : AncientLimitFlow n) (κ : ℝ) : Prop :=
  let C := L.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  ∀ r₀ : ℝ, 0 < r₀ → ∀ t : ℝ, t < 0 → ∀ p : C.carrier,
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (L.flow.metric t).ball p r,
        |(L.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ calibratedMetricVolume (L.flow.metric t)
        ((L.flow.metric t).ball p r)


structure AsymptoticSolitonLimit {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) where
  convergence : AncientGeometricConvergence S
  nonflat : ∃ t : ℝ, t < 0 ∧
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

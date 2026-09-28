import PoincareConjecture.Definitions.Ch05.Compactness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure PointedFlowSequence (n : ℕ) (T' T : ℝ) where
  carrier : ℕ → FlowCarrier n
  flow : ∀ k, BasedFlow n T' T (carrier k)

noncomputable def pullbackInnerValue {n : ℕ} {T' T : ℝ}
    {L C : FlowCarrier n} (F : BasedFlow n T' T L) (G : BasedFlow n T' T C)
    {domain : Set (ℝ × L.carrier)}
    (e : SmoothSpacetimeEmbedding F G domain)
    (t : ℝ) (x : L.carrier) (v w : L.tangent x) : ℝ :=
  letI : TopologicalSpace L.carrier := L.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
  letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let ψ : L.carrier → C.carrier := fun y ↦ (e.toFun (t, y)).2
  (G.flow.metric t).inner (ψ x)
    (mfderiv (𝓡 n) (𝓡 n) ψ x v)
    (mfderiv (𝓡 n) (𝓡 n) ψ x w)

structure PointedGeometricConvergence {n : ℕ} {T' T : ℝ}
    (S : PointedFlowSequence n T' T) where
  limitCarrier : FlowCarrier n
  limitFlow : BasedFlow n T' T limitCarrier
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : ℕ → Set limitCarrier.carrier
  exhaustion_open : ∀ j,
    letI : TopologicalSpace limitCarrier.carrier := limitCarrier.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j,
    letI : TopologicalSpace limitCarrier.carrier := limitCarrier.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j,
    letI : TopologicalSpace limitCarrier.carrier := limitCarrier.topologicalSpace
    IsCompact (closure (exhaustion j))
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  embedding : ∀ j,
    SmoothSpacetimeEmbedding
      limitFlow (S.flow (subsequence j))
      (Set.Ioo T' T ×ˢ exhaustion j)
  base_in_exhaustion : ∀ j, limitFlow.base ∈ exhaustion j
  base_preserving : ∀ j,
    (embedding j).toFun (0, limitFlow.base) =
      (0, (S.flow (subsequence j)).base)
  pullback_metric_converges :
    letI : TopologicalSpace limitCarrier.carrier := limitCarrier.topologicalSpace
    ∀ j K I, IsCompact K → K ⊆ exhaustion j → IsCompact I →
      I ⊆ Set.Ioo T' T → ∀ ε > 0, ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
          ∀ t ∈ I, ∀ x ∈ K, ∀ v w : limitCarrier.tangent x,
            limitCarrier.metricNorm (limitFlow.metricAt t) x v ≤ 1 →
            limitCarrier.metricNorm (limitFlow.metricAt t) x w ≤ 1 →
            |pullbackInnerValue limitFlow (S.flow (subsequence k)) (embedding k) t x v w -
              limitCarrier.metricInner (limitFlow.metricAt t) x v w| < ε

  pullback_metric_CInfinity :
    letI : TopologicalSpace limitCarrier.carrier := limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) limitCarrier.carrier :=
      limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ limitCarrier.carrier := limitCarrier.isManifold
    ∀ q : limitCarrier.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ {p | p.1 ∈ Set.Ioo T' T ∧
        p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ p ∈ K,
          ‖MetricJet r
              (FlowCarrier.coordinateCoefficient limitCarrier q
                (pullbackInnerValue limitFlow (S.flow (subsequence k)) (embedding k))
                a b) K p -
            MetricJet r
              (FlowCarrier.coordinateCoefficient limitCarrier q
                (fun t x v w ↦ limitCarrier.metricInner (limitFlow.metricAt t) x v w)
                a b) K p‖ < ε

structure PointedRicciFlowCompactnessHypotheses (n : ℕ) (T' T : ℝ) where
  time_bounds : T' < 0 ∧ 0 < T
  sequence : PointedFlowSequence n T' T
  volume_compatibility : ∀ k, (sequence.flow k).volumeCompatible
  zero_time_ball_compact :
    ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
      let C := sequence.carrier k
      let F := sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      IsCompact (closure (F.zeroBall A))
  spacetime_control :
    ∀ A : ℝ, 0 < A → ∀ I : Set ℝ, IsCompact I → I.OrdConnected →
      0 ∈ I → I ⊆ Set.Ioo T' T → ∃ K : ℝ, 0 ≤ K ∧
        ∀ᶠ k : ℕ in Filter.atTop, ∃ e : SpacetimeEmbedding
            (sequence.flow k) (sequence.flow k) A I,
          (∀ x ∈ (sequence.flow k).zeroBall A, (e.toFun (0, x)).2 = x) ∧
          CurvatureBoundOn (sequence.flow k) (sequence.flow k) A I e K

  all_time_curvature_control :
    ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        let C := sequence.carrier k
        let F := sequence.flow k
        letI : TopologicalSpace C.carrier := C.topologicalSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
        letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
        ∀ t₀ ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
          ∀ x ∈ F.ballAt t₀ A,
            (F.flow.connection t).curvatureTensorNorm x ≤ K
  noncollapsing : ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 < κ ∧
    ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal (κ * r₀ ^ n) ≤ (sequence.flow k).zeroBallVolume r₀

structure PointedRicciFlowCompactnessConclusion
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T) where
  geometric_limit : PointedGeometricConvergence H.sequence
  complete_interior : ∀ t ∈ Set.Ioo T' T,
    FlowCarrier.metricComplete geometric_limit.limitCarrier
      (geometric_limit.limitFlow.metricAt t)

end PoincareConjecture

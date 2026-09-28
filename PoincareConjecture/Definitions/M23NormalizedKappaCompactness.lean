import PoincareConjecture.Definitions.Ch09.NormalizedKappaCompactness










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure NormalizedKappaCompactnessData where
  kappa : ℝ
  kappa_pos : 0 < kappa
  sequence : NormalizedKappaSolutionSequence kappa





structure M23InteriorConvergence
    {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa) where
  limit : BasedKappaSolution kappa
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : ℕ → Set limit.carrier.carrier
  exhaustion_open : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsCompact (closure (exhaustion j))
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  time_window : ℕ → Set ℝ


  time_window_interval : ∀ j, ∃ a b : ℝ,
    a < b ∧ time_window j = Set.Icc a b
  time_window_compact : ∀ j, IsCompact (time_window j)
  time_window_subset_ancient : ∀ j, time_window j ⊆ Set.Iio 0
  time_window_increasing : ∀ j, time_window j ⊆ time_window (j + 1)
  time_window_covers : ⋃ j, time_window j = Set.Iio 0
  embedding : ∀ j,
    NormalizedKappaSpacetimeEmbedding
      (source := S.term (subsequence j)) (target := limit)
      (time_window j ×ˢ exhaustion j)
  base_in_exhaustion : ∀ j, limit.base ∈ exhaustion j
  base_preserving : ∀ j t, t ∈ time_window j →
    (embedding j).toFun (t, limit.base) =
      (t, (S.term (subsequence j)).base)


  pullback_metric_CInfinity :
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := limit.connectedSpace
    ∀ q : C.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact K →
      K ⊆ {p | p.1 ∈ time_window j ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
        (extChartAt (𝓡 3) q).symm p.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin 3, ∀ p ∈ K,
          ‖iteratedFDerivWithin ℝ r
              (normalizedKappaPullbackCoefficient
                (source := S.term (subsequence k)) (target := limit)
                (embedding k) q a b)
              (time_window j ×ˢ Set.univ) p -
            iteratedFDerivWithin ℝ r
              (FlowCarrier.coordinateCoefficient C q
                (fun t x v w ↦
                  (limit.flow.flow.metric t).inner x v w) a b)
              (time_window j ×ˢ Set.univ) p‖ < ε

end PoincareConjecture

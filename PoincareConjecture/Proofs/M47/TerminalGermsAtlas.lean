import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Metric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

open ChartDistance



theorem terminalGerms_terminal_atlas
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k i))
    (g : ∀ k, RiemannianMetric 3 (M k))
    (hjets : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i))))
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤
          (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    (B : ℕ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hB : ∀ i, TendstoLocallyUniformlyOn
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
      (B i) atTop (U i))
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (U i)) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := overlapSystem hD L he c hc hlower hopen hconn
    T2Space (Quotient O.setoid) ∧ SecondCountableTopology (Quotient O.setoid) ∧
      ∃ hO : SmoothOverlap U hU O,
        ∃ gLimit : ∀ i, CanonicalMetric U hU i,
          ∃ hcompat : CompatibleMetrics U hU O gLimit,
            (∀ i (x : Piece U i) v w, (gLimit i).inner x v w = B i x v w) ∧
            letI := quotientChartedSpace U hU O
            letI := quotient_isManifold U hU O hO
            ∀ i (x : Piece U i) (v w : TangentSpace (𝓡 3) x),
              B i x v w = (quotientMetric U hU O hO gLimit hcompat).inner (O.include i x)
                (mfderiv (𝓡 3) (𝓡 3) (O.include i) x v)
                (mfderiv (𝓡 3) (𝓡 3) (O.include i) x w) := by
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let O := overlapSystem hD L he c hc hlower hopen hconn
  have htransition := fun i j => locallyEventuallyBoundedDerivatives_source_transition
    U hU hD L he c hc hlower hopen hconn hsmooth g hjets helliptic i j
  let hO : SmoothOverlap U hU O :=
    overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth htransition
  obtain ⟨gLimit, hcoeff, hcompat⟩ := exists_compatibleMetrics_of_coordinate_limits
    U hU hD L he c hc hlower hopen hconn hsmooth g B hB hBsmooth (by
      intro i x hx
      obtain ⟨a, ha, hbound⟩ := helliptic i {x} isCompact_singleton
        (singleton_subset_iff.mpr hx)
      exact ⟨a, ha, hbound.mono fun k hk v => hk x (mem_singleton x) v⟩) htransition
  refine ⟨O.quotient_t2Space (overlapSystem_closed hD L he c hc hlower hopen hconn),
    O.quotient_secondCountableTopology, hO, gLimit, hcompat, hcoeff, ?_⟩
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  intro i x v w
  exact (hcoeff i x v w).symm.trans
    (quotientMetric_preserves U hU O hO gLimit hcompat i x v w)

end PoincareConjecture.M47

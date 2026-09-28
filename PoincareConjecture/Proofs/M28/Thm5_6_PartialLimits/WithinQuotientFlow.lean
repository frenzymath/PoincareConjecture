import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinLocalFlows
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricFamilies
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.RicciFlow












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance





theorem exists_quotientRicciFlow_of_within_spacetime_bounds
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    (hconvU : ∀ i, Convex ℝ (U i)) [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hconvJ : Convex ℝ J)
    [∀ i, LocallyCompactSpace (J ×ˢ U i)] (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (Fseq : ∀ k, RicciFlow n (M k) J)
    (hjets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ p ∈ K,
        ‖iteratedFDerivWithin ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients
              (chartParametrization U hU (e k i)) z.2) (J ×ˢ U i) p‖ ≤ C)
    (hpositive : ∀ t ∈ J, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        ((Fseq k).metric t).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := overlapSystem hD L he c hc hlower hopen hconn
    let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ i j x y, Tendsto (fun k => dist (e (σ k) i x) (e (σ k) j y)) atTop
        (𝓝 (D i j (x, y)))) ∧
      ∃ B : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        (∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i)) ∧
        (∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((Fseq (σ k)).metric z.1).pullbackCoefficients
                (chartParametrization U hU (e (σ k) i)) z.2) (J ×ˢ U i))
          (iteratedFDerivWithin ℝ m (B i) (J ×ˢ U i)) atTop K) ∧
        ∃ (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
          (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t)),
          (∀ t ∈ J, ∀ i (x : Piece U i) v w,
            (gLimit t i).inner x v w = B i (t, x) v w) ∧
          (∀ i, RiemannianMetric.IsSmoothFamilyOn (fun t => gLimit t i) J) ∧
          ∃ FQ : RicciFlow n (Quotient O.setoid) J,
            FQ.metric = fun t => quotientMetric U hU O hO (gLimit t) (hcompat t) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let O := overlapSystem hD L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  obtain ⟨σ, hσ, hDσ, B, hBsmooth, hBjets, gLimit, hcompat, hcoeff, hfamily, _⟩ :=
    exists_smooth_metricFamilies_of_within_spacetime_bounds U hU hconvU hD L he c hc
      hlower hopen hconn hsmooth hJ hconvJ t₀ ht₀
      (fun k => (Fseq k).metric) (fun k => (Fseq k).smooth) hjets hpositive hbound
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) J,
      F.metric = fun t => gLimit t i := by
    intro i
    exact exists_ricciFlow_on_within_coordinate_limit U hU hJ (fun k => Fseq (σ k)) i
      (fun k => e (σ k) i) (fun k => hsmooth (σ k) i)
      (fun t => gLimit t i) (hfamily i) (B i)
      (fun t ht => hcoeff t ht i) (hBjets i)
  choose F hF using hlocal
  obtain ⟨FQ, hFQ⟩ := exists_quotientRicciFlow_of_chart_flows U hU O hO
    gLimit hcompat F hF
  exact ⟨σ, hσ, hDσ, B, hBsmooth, hBjets, gLimit, hcompat, hcoeff, hfamily, FQ, hFQ⟩

end PoincareConjecture.ChartDistance

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.RicciFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.RicciFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_ancient_quotientRicciFlow_of_chart_limits
    {ι : Type*} [Nonempty ι] {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (e : ∀ k i, Piece U i → M k)
    (D : ∀ i j, C(Piece U i × Piece U j, ℝ))
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {T : ℝ} (hT : 0 < T) {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Iio T ×ˢ U i))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric z.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hpositive : ∀ t ∈ Iio T, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := overlapSystem hD L he c hc hlower hopen hconn
    let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ (g : ℝ → ∀ i, CanonicalMetric U hU i)
      (hcompat : ∀ t, CompatibleMetrics U hU O (g t))
      (F : RicciFlow n (Quotient O.setoid) (Iio T)),
      F.metric = (fun t => quotientMetric U hU O hO (g t) (hcompat t)) ∧
      ∀ t ∈ Iio T, ∀ i (x : Piece U i) v w,
        (g t i).inner x v w = B i (t, x) v w := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let O := overlapSystem hD L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hBlocal (i : ι) : TendstoLocallyUniformlyOn
      (fun k z => ((Fseq k).metric z.1).pullbackCoefficients
        (chartParametrization U hU (e k i)) z.2)
      (B i) atTop (Iio T ×ˢ U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (isOpen_Iio.prod (hU i)) (hBjets i 0)
  have hBslice : ∀ t ∈ Iio T, ∀ i, TendstoLocallyUniformlyOn
      (fun k => ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)))
      (fun x => B i (t, x)) atTop (U i) := by
    intro t ht i
    exact (hBlocal i).comp (fun x => (t, x)) (fun _ hx => ⟨ht, hx⟩)
      (continuous_const.prodMk continuous_id).continuousOn
  obtain ⟨g, hcompat, hcoeff, hfamily, _⟩ :=
    exists_compatibleMetricFamilies_of_spacetime_limits U hU hD L he c hc hlower
      hopen hconn hsmooth 0 hT (fun k => (Fseq k).metric) B hBslice
      hBsmooth hpositive hbound
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) (Iio T),
      F.metric = fun t => g t i := by
    intro i
    exact exists_ancientRicciFlow_on_coordinate_limit U hU Fseq htime
      i (fun k => e k i) (fun k => hsmooth k i) (fun t => g t i)
      (hfamily i) (B i) (fun t ht => hcoeff t ht i) (hBjets i)
  choose Fchart hFchart using hlocal
  obtain ⟨FQ, hFQ⟩ := exists_quotientRicciFlow_of_chart_flows U hU O hO
    g hcompat Fchart hFchart
  exact ⟨g, hcompat, FQ, hFQ, hcoeff⟩

end PoincareConjecture.ChartDistance

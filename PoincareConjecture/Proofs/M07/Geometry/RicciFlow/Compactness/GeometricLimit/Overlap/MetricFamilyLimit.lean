import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CoordinateFamily
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricFamily











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
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

include hD he hc hlower hopen hconn hsmooth in



theorem exists_compatibleMetricFamilies_of_spacetime_limits
    {J : Set ℝ} (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ t ∈ J, ∀ i, TendstoLocallyUniformlyOn
      (fun k => (g k t).pullbackCoefficients (chartParametrization U hU (e k i)))
      (fun x => B i (t, x)) atTop (U i))
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i))
    (hBlower : ∀ t ∈ J, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        (g k t).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
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
    ∃ (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
      (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t)),
      (∀ t ∈ J, ∀ i (x : Piece U i) v w, (gLimit t i).inner x v w = B i (t, x) v w) ∧
      (∀ i, RiemannianMetric.IsSmoothFamilyOn (fun t => gLimit t i) J) ∧
      RiemannianMetric.IsSmoothFamilyOn
        (fun t => quotientMetric U hU O hO (gLimit t) (hcompat t)) J := by
  classical
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let O := overlapSystem hD L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hex : ∀ t : J, ∃ gSlice : ∀ i, CanonicalMetric U hU i,
      (∀ i (x : Piece U i) v w, (gSlice i).inner x v w = B i (t, x) v w) ∧
      CompatibleMetrics U hU O gSlice := by
    intro t
    apply exists_compatibleMetrics_of_coordinate_limits U hU hD L he c hc hlower hopen hconn
      hsmooth (fun k => g k t) (fun i x => B i (t, x)) (hB t t.property) ?_
      (hBlower t t.property) hbound
    intro i
    have hmap : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin n) => ((t : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    have hmaps : MapsTo (fun x : EuclideanSpace ℝ (Fin n) => ((t : ℝ), x))
        (U i) (J ×ˢ U i) := fun _ hx => ⟨t.property, hx⟩
    exact (hBsmooth i).comp hmap.contDiffOn hmaps
  choose gSlice hcoeffSlice hcompatSlice using hex
  let gLimit : ℝ → ∀ i, CanonicalMetric U hU i := fun t =>
    if ht : t ∈ J then gSlice ⟨t, ht⟩ else gSlice ⟨t₀, ht₀⟩
  have hcoeff : ∀ t ∈ J, ∀ i (x : Piece U i) v w,
      (gLimit t i).inner x v w = B i (t, x) v w := by
    intro t ht i x v w
    simpa only [gLimit, dif_pos ht] using hcoeffSlice ⟨t, ht⟩ i x v w
  have hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t) := by
    intro t
    by_cases ht : t ∈ J
    · simpa only [gLimit, dif_pos ht] using hcompatSlice ⟨t, ht⟩
    · simpa only [gLimit, dif_neg ht] using hcompatSlice ⟨t₀, ht₀⟩
  have hfamily : ∀ i, RiemannianMetric.IsSmoothFamilyOn (fun t => gLimit t i) J := by
    intro i
    exact canonicalMetric_isSmoothFamilyOn_of_coefficients U hU i
      (fun t => gLimit t i) (B i) (hBsmooth i) (fun t ht => hcoeff t ht i)
  refine ⟨gLimit, hcompat, hcoeff, hfamily, ?_⟩
  exact quotientMetric_isSmoothFamilyOn U hU O hO (fun i t => gLimit t i) hfamily hcompat

end PoincareConjecture.ChartDistance

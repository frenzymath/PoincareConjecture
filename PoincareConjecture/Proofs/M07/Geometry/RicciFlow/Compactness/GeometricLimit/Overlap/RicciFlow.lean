import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricFamilyExtraction
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Descent









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance



theorem exists_quotientRicciFlow_of_chart_flows_with_connection
    {ι : Type*} [Nonempty ι] {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {J : Set ℝ} (g : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (g t))
    (F : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i, RicciFlow n (Piece U i) J)
    (hF : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i, (F i).metric = fun t => g t i)
    (t₀ : ℝ)
    (D₀ : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      LeviCivitaData (quotientMetric U hU O hO (g t₀) (hcompat t₀))) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ FQ : RicciFlow n (Quotient O.setoid) J,
      FQ.metric = fun t => quotientMetric U hU O hO (g t) (hcompat t) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hg : ∀ i, RiemannianMetric.IsSmoothFamilyOn (fun t => g t i) J := by
    intro i
    rw [← hF i]
    exact (F i).smooth
  apply RicciFlow.exists_of_covering_local_diffeomorphisms F
    (fun t => quotientMetric U hU O hO (g t) (hcompat t))
    (quotientMetric_isSmoothFamilyOn U hU O hO (fun i t => g t i) hg hcompat)
    t₀ D₀ O.include (include_isLocalDiffeomorph U hU O hO)
  · intro y
    have hy : y ∈ ⋃ i, Set.range (O.include i) := by rw [O.include_cover]; trivial
    simpa only [mem_iUnion, mem_range] using hy
  · intro t _ i x a b
    rw [hF i]
    exact quotientMetric_preserves U hU O hO (g t) (hcompat t) i x a b



theorem exists_quotientRicciFlow_of_spacetime_limits_with_connection
    {ι : Type*} [Nonempty ι] {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} (hJ : IsOpen J) (Fseq : ∀ k, RicciFlow n (M k) J)
    (e : ∀ k i, Piece U i → M k)
    (he : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (g : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (g t))
    (hg : ∀ i,
      letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      RiemannianMetric.IsSmoothFamilyOn (fun t => g t i) J)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ J, ∀ i (x : Piece U i) v w, (g t i).inner x v w = B i (t, x) v w)
    (hjets : ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) p.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (t₀ : ℝ)
    (D₀ : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      LeviCivitaData (quotientMetric U hU O hO (g t₀) (hcompat t₀))) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ FQ : RicciFlow n (Quotient O.setoid) J,
      FQ.metric = fun t => quotientMetric U hU O hO (g t) (hcompat t) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) J,
      F.metric = fun t => g t i := by
    intro i
    exact exists_ricciFlow_on_coordinate_limit U hU hJ Fseq i (fun k => e k i)
      (fun k => he k i) (fun t => g t i) (hg i) (B i)
      (fun t ht => hcoeff t ht i) (hjets i)
  choose F hF using hlocal
  exact exists_quotientRicciFlow_of_chart_flows_with_connection U hU O hO
    g hcompat F hF t₀ D₀



theorem exists_quotientRicciFlow_of_chart_flows
    {ι : Type*} [Nonempty ι] {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {J : Set ℝ} (g : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (g t))
    (F : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i, RicciFlow n (Piece U i) J)
    (hF : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i, (F i).metric = fun t => g t i) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ FQ : RicciFlow n (Quotient O.setoid) J,
      FQ.metric = fun t => quotientMetric U hU O hO (g t) (hcompat t) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hq := include_isLocalDiffeomorph U hU O hO
  have hcover : ∀ y, ∃ i x, O.include i x = y := by
    intro y
    have hy : y ∈ ⋃ i, Set.range (O.include i) := by rw [O.include_cover]; trivial
    simpa only [mem_iUnion, mem_range] using hy
  let D₀ := (quotientMetric U hU O hO (g 0) (hcompat 0)).leviCivitaDataOfCover
    (g 0) (fun i => RiemannianMetric.canonicalMetricLeviCivitaData (U i) (hU i) (g 0 i))
    O.include (fun i => (hq i).contMDiff)
    (fun i x => ⟨(hq i x).mfderivToContinuousLinearEquiv (by simp), rfl⟩)
    (quotientMetric_preserves U hU O hO (g 0) (hcompat 0)) hcover
  exact exists_quotientRicciFlow_of_chart_flows_with_connection U hU O hO
    g hcompat F hF 0 D₀





theorem exists_quotientRicciFlow_of_spacetime_bounds
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
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
    {J : Set ℝ} (hJ : IsOpen J) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (Fseq : ∀ k, RicciFlow n (M k) J)
    (hjets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients
              (chartParametrization U hU (e k i)) z.2) p‖ ≤ C)
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
          (fun k => iteratedFDeriv ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((Fseq (σ k)).metric z.1).pullbackCoefficients
                (chartParametrization U hU (e (σ k) i)) z.2))
          (iteratedFDeriv ℝ m (B i)) atTop K) ∧
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
    exists_smooth_metricFamilies_of_spacetime_bounds U hU hD L he c hc hlower hopen
      hconn hsmooth hJ t₀ ht₀ (fun k => (Fseq k).metric) (fun k => (Fseq k).smooth)
      hjets hpositive hbound
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) J,
      F.metric = fun t => gLimit t i := by
    intro i
    exact exists_ricciFlow_on_coordinate_limit U hU hJ (fun k => Fseq (σ k)) i
      (fun k => e (σ k) i) (fun k => hsmooth (σ k) i)
      (fun t => gLimit t i) (hfamily i) (B i)
      (fun t ht => hcoeff t ht i) (hBjets i)
  choose F hF using hlocal
  obtain ⟨FQ, hFQ⟩ := exists_quotientRicciFlow_of_chart_flows U hU O hO
    gLimit hcompat F hF
  exact ⟨σ, hσ, hDσ, B, hBsmooth, hBjets, gLimit, hcompat, hcoeff, hfamily, FQ, hFQ⟩

end PoincareConjecture.ChartDistance

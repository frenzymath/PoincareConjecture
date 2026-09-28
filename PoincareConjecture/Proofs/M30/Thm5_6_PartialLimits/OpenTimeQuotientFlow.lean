import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.OpenTimeCoordinateFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.RicciFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open PoincareConjecture.ChartDistance
open scoped Topology NNReal Manifold ContDiff

universe u v

namespace PoincareConjecture.M30

theorem exists_quotientFlow_of_chart_limits_on_open_time
    {ι : Type u} [Nonempty ι] {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type v} [∀ k, MetricSpace (M k)]
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
    {W : Set ℝ} (hW : IsOpen W) (hWord : Set.OrdConnected W)
    (hzero : (0 : ℝ) ∈ W)
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (W ×ˢ U i))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hpositive : ∀ t ∈ W, ∀ i x, x ∈ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
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
      (F : RicciFlow n (Quotient O.setoid) W),
      F.metric = (fun t => quotientMetric U hU O hO (g t) (hcompat t)) ∧
      (∀ t ∈ W, ∀ i (x : Piece U i) v w,
        (g t i).inner x v w = B i (t, x) v w) ∧
      ∀ i m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients
              (chartParametrization U hU (e k i)) z.2))
        (iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (F.metric z.1).pullbackCoefficients
              (chartParametrization U hU (O.include i)) z.2)) atTop K := by
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
  have hWne : W.Nontrivial := by
    obtain ⟨a, b, _, habnhds, habW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds hzero)
    have hab : (0 : ℝ) ∈ Ioo a b := Icc_mem_nhds_iff.mp habnhds
    refine ⟨0, hzero, b / 2, habW ⟨?_, ?_⟩, ?_⟩ <;>
      rcases hab with ⟨ha, hb⟩ <;> linarith
  have hBlocal (i : ι) : TendstoLocallyUniformlyOn
      (fun k z => ((Fseq k).metric z.1).pullbackCoefficients
        (chartParametrization U hU (e k i)) z.2)
      (B i) atTop (W ×ˢ U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (hW.prod (hU i)) (hBjets i 0)
  have hBslice : ∀ t ∈ W, ∀ i, TendstoLocallyUniformlyOn
      (fun k => ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)))
      (fun x => B i (t, x)) atTop (U i) := by
    intro t ht i
    exact (hBlocal i).comp (fun x => (t, x)) (fun _ hx => ⟨ht, hx⟩)
      (continuous_const.prodMk continuous_id).continuousOn
  obtain ⟨g, hcompat, hcoeff, hfamily, _⟩ :=
    exists_compatibleMetricFamilies_of_spacetime_limits U hU hD L he c hc hlower
      hopen hconn hsmooth 0 hzero (fun k => (Fseq k).metric) B hBslice
      hBsmooth hpositive hbound
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) W,
      F.metric = fun t => g t i := by
    intro i
    exact exists_coordinate_flow_of_expanding_time_domains U hU hW hWord hWne
      Fseq htime i (fun k => e k i) (fun k => hsmooth k i) (fun t => g t i)
      (hfamily i) (B i) (fun t ht => hcoeff t ht i) (hBjets i)
  choose Fchart hFchart using hlocal
  obtain ⟨F, hF⟩ := exists_quotientRicciFlow_of_chart_flows U hU O hO
    g hcompat Fchart hFchart
  refine ⟨g, hcompat, F, hF, hcoeff, ?_⟩
  intro i m K hK hKW
  have hQcoeff : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (F.metric z.1).pullbackCoefficients
          (chartParametrization U hU (O.include i)) z.2)
      (B i) (W ×ˢ U i) := by
    rw [hF]
    exact quotientMetric_family_pullbackCoefficients_eqOn U hU O hO
      (fun i t => g t i) hcompat B hcoeff i
  exact (hBjets i m K hK hKW).congr_right
    ((eqOn_iteratedFDeriv_of_isOpen (hW.prod (hU i)) hQcoeff.symm m).mono hKW)

end PoincareConjecture.M30

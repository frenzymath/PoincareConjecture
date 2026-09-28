import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticCompleteness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Metric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChosenChart
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.PointedExhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M30

open ChartDistance

theorem exists_complete_static_limit_of_coordinate_limits
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
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
    {i₀ : ℕ} (p : Piece U i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (g : ∀ k, RiemannianMetric n (M k))
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (U i))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((g k).pullbackCoefficients (chartParametrization U hU (e k i))))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hpositive : ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v) :
    ∃ G : PartialPointedMetricConvergence g (fun k => e k i₀ p) 1,
      G.limitCarrier.metricComplete G.limitMetric ∧
        ∀ R : ℝ, 0 < R → ∃ l : ℕ, ∀ᶠ k in atTop,
          (g (G.subsequence k)).ball (e (G.subsequence k) i₀ p) R ⊆
            G.embedding k '' G.exhaustion l := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let hp := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hp L he c hc hlower hopen hconn hsmooth hbound
  let hclosed := overlapSystem_closed hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, sigma, hsigma,
      f, hf, happrox, hreadout, hescape⟩ :=
    exists_pointed_source_exhaustion_with_boundary_escape U hU hD L he c hc hlower
      hopen hconn hsmooth hbound p hcover
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have hBlocal (i : ℕ) : TendstoLocallyUniformlyOn
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
      (B i) atTop (U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hU i) (hBjets i 0)
  obtain ⟨gLimit, hcoeff, hcompat⟩ :=
    exists_compatibleMetrics_of_coordinate_limits U hU hp L he c hc hlower
      hopen hconn hsmooth g B hBlocal hBsmooth hpositive hbound
  let C := O.flowCarrier U hU hO hclosed
  let gQ := quotientMetric U hU O hO gLimit hcompat
  have hsourceJets := source_exhaustion_pullbackCoefficients_tendsto_jets
    U hU O hO hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (sigma k)) c hc (fun k => hlower (sigma k))
    (fun k => hopen (sigma k)) (fun k => hconn (sigma k))
    (fun k => hsmooth (sigma k)) happrox hreadout (fun k => g (sigma k)) B hBsmooth
    (fun i m K hK hKU V hV =>
      hsigma.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
  have hboundary (R : ℝ) (hR : 0 < R) :
      ∃ l : ℕ, ∀ᶠ k in atTop, ∀ q ∈ frontier (E l),
        ENNReal.ofReal R ≤ (g (sigma k)).edist (e (sigma k) i₀ p) (f k q) := by
    obtain ⟨l, hl⟩ := hescape R hR
    exact ⟨l, hl.mono fun k hk q hq => by simpa only [hdist] using hk q hq⟩
  let G : PartialPointedMetricConvergence g (fun k => e k i₀ p) 1 := {
    limitCarrier := C
    limitMetric := gQ
    base := O.include i₀ p
    subsequence := sigma
    subsequence_strictMono := hsigma
    exhaustion := E
    exhaustion_open := hE
    exhaustion_connected := hEc
    base_in_exhaustion := hEp
    exhaustion_compactClosure := hEK
    exhaustion_step := hEstep
    exhaustion_covers := hEcover
    embedding := f
    embedding_open := fun k => (hf k).1
    embedding_smooth := fun k => (hf k).2.1
    base_preserving := fun k => (hf k).2.2
    metric_jets := by
      intro q m K hK hKchart
      obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q
      have hKU : K ⊆ U i := by simpa only [htarget] using hKchart
      rw [hinverse]
      have hlimit : EqOn
          (gQ.pullbackCoefficients (chartParametrization U hU (O.include i))) (B i) (U i) :=
        quotientMetric_pullbackCoefficients_eqOn U hU O hO gLimit hcompat B hcoeff i
      apply (hsourceJets i m K hK hKU).congr_right
      intro x hx
      exact ((eqOn_iteratedFDeriv_of_isOpen (hU i) hlimit m) (hKU hx)).symm
    boundary_control := by
      intro R hR
      obtain ⟨l, hl⟩ := hboundary 1 zero_lt_one
      exact ⟨l, hl.mono fun k hk q hq =>
        (ENNReal.ofReal_le_ofReal hR.le).trans (hk q hq)⟩ }
  have hcoverage (R : ℝ) (hR : 0 < R) :
      ∃ l : ℕ, ∀ᶠ k in atTop,
        (g (G.subsequence k)).ball (e (G.subsequence k) i₀ p) R ⊆
          G.embedding k '' G.exhaustion l :=
    G.source_ball_coverage_of_boundary_control hR (hboundary R hR)
  exact ⟨G, G.metricComplete_of_source_ball_coverage hcoverage, hcoverage⟩

end PoincareConjecture.M30

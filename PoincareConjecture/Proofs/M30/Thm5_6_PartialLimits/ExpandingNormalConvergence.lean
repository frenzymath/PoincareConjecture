import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ExpandingChartBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.OpenTimePointedConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Rescaling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open PoincareConjecture.NormalChartCover
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space




theorem exists_complete_reference_convergence_of_expanding_normal_charts
    {n : ℕ} {s' s : ℝ}
    (Href : PointedRicciFlowCompactnessHypotheses n s' s)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (Href.sequence.carrier k).carrier (J k))
    (hmetric : ∀ k, (Fseq k).metric = (Href.sequence.flow k).flow.metric)
    {W : Set ℝ} (hW : IsOpen W) (hWord : W.OrdConnected)
    (hwindow : Ioo s' s ⊆ W)
    (htime : ∀ a b : ℝ, Icc a b ⊆ W → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ W →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc a b, ∀ x : (Href.sequence.carrier k).carrier,
          ((Fseq k).connection t).curvatureTensorNorm x ≤ C)
    {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k →
      NormalChartCover (Href.sequence.flow k).flow.metric
        (Href.sequence.flow k).base s' s ((j : ℝ) + 1)
        (R j) (ρ j) (a j) (b j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) :
    ∃ G : PointedGeometricConvergence Href.sequence,
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ∃ F : RicciFlow n G.limitCarrier.carrier W,
        F.metric = G.limitFlow.flow.metric ∧
        G.limitCarrier.metricComplete (F.metric 0) ∧
        ∀ q' : G.limitCarrier.carrier, ∀ m : ℕ,
          ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
          K ⊆ W ×ˢ (extChartAt (𝓡 n) q').target → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                ((Fseq (G.subsequence k)).metric z.1).pullbackCoefficients
                  ((fun x => ((G.embedding k).toFun (0, x)).2) ∘
                    (extChartAt (𝓡 n) q').symm) z.2))
            (iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                (F.metric z.1).pullbackCoefficients
                  (extChartAt (𝓡 n) q').symm z.2)) atTop K := by
  classical
  let : ∀ k, MetricSpace (Href.sequence.carrier k).carrier :=
    fun k => (Href.sequence.carrier k).metricSpaceOf ((Href.sequence.flow k).metricAt 0)
  have hzero : (0 : ℝ) ∈ W := hwindow Href.time_bounds
  have hraw := referenceNormalChartCoefficients_on_expanding_time_domains
    Href hShi Fseq hmetric hW hWord hzero htime hcurv cover hρ hρR ha hb
  have hhalf : ∀ j, ρ j / 2 ≤ R j := by
    intro j
    linarith [hρ j, hρR j]
  let U := fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1
  have hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, by simp [U]⟩⟩
  let e := diagonalUnitBallMap cover
  choose L c hc hL hlower using diagonalUnitBallMap_distance_bounds cover hρ ha
  have hpositive (i : ℕ) (t : ℝ) (ht : t ∈ W) :=
    diagonalUnitBallMap_eventually_lower_coefficients_of_raw cover hρ hhalf i t
      ((hraw i).2.2 t ht)
  apply exists_complete_reference_convergence_on_open_time Href.sequence Href.time_bounds
    hW hWord hwindow Fseq hmetric htime U hU e L
    (by
      intro k i
      have hdist := (hL i k).dist_le_mul
      let : MetricSpace (Href.sequence.carrier k).carrier :=
        (Href.sequence.carrier k).metricSpaceOf ((Fseq k).metric 0)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using
        hdist x y) c hc
    (by
      intro k i x y
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using
        hlower i k x y)
    (diagonalUnitBallMap_isOpenEmbedding cover hρ hhalf)
    (diagonalUnitBallMap_isLocalDiffeomorph cover hρ hhalf)
    (by
      intro i j x y
      obtain ⟨B, hB⟩ := diagonalUnitBallMap_pairwise_bounded cover L
        (fun k i => hL i k) i j x y
      refine ⟨B, fun k => ?_⟩
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using hB k)
    (i₀ := 0) ⟨0, by simp [U]⟩ (diagonalUnitBallMap_zero cover)
  · intro A hA
    obtain ⟨v, K, hK, hcov⟩ := diagonalUnitBallMap_compact_cover cover hρ A hA
    refine ⟨v, K, hK, ?_⟩
    filter_upwards [hcov] with k hk
    simpa only [FlowCarrier.metricBall_eq_metricBallOf, hmetric, BasedFlow.metricAt,
      e, diagonalUnitBallMap_zero] using hk
  · intro i K _ hKU
    obtain ⟨d, hd, hbound⟩ := hpositive i 0 hzero
    refine ⟨d, hd, ?_⟩
    simpa only [hmetric] using hbound.mono
      (fun k hk x hx v => hk x (hKU hx) v)
  · intro i
    simpa only [hmetric] using
      diagonalUnitBallMap_eventually_bounded_spacetime_derivatives_on_open
        cover hρ hhalf i hW (hraw i).1 (hraw i).2.1
  · intro t ht i x hx
    obtain ⟨d, hd, hbound⟩ := hpositive i t ht
    refine ⟨d, hd, ?_⟩
    simpa only [hmetric] using hbound.mono (fun k hk v => hk x hx v)

end PoincareConjecture.M30

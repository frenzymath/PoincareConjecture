import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SourceEmbeddings
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Metric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChosenChart
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_partial_metric_limit_of_coordinate_limits
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
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
    {i₀ : ℕ} (p : Piece U i₀) (A : ℝ) (hA : 0 < A)
    (hrange : ∀ i (x : Piece U i), D i₀ i (p, x) < A)
    (hcover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
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
    Nonempty (M28.PartialPointedMetricConvergence g (fun k => e k i₀ p) A) := by
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
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ,
      f, hf, happrox, hreadout, hboundary⟩ :=
    exists_partial_pointed_source_exhaustion U hU hD L he c hc hlower hopen hconn
      hsmooth hbound p A hA hrange hcover
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
    L (fun k => he (σ k)) c hc (fun k => hlower (σ k))
    (fun k => hopen (σ k)) (fun k => hconn (σ k)) (fun k => hsmooth (σ k))
    happrox hreadout (fun k => g (σ k)) B hBsmooth
    (fun i m K hK hKU V hV => hσ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
  refine ⟨{
    limitCarrier := C
    limitMetric := gQ
    base := O.include i₀ p
    subsequence := σ
    subsequence_strictMono := hσ
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
    metric_jets := ?_
    boundary_control := ?_ }⟩
  · intro q m K hK hKchart
    obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q
    have hKU : K ⊆ U i := by simpa only [htarget] using hKchart
    rw [hinverse]
    have hlimit : EqOn
        (gQ.pullbackCoefficients (chartParametrization U hU (O.include i))) (B i) (U i) :=
      quotientMetric_pullbackCoefficients_eqOn U hU O hO gLimit hcompat B hcoeff i
    apply (hsourceJets i m K hK hKU).congr_right
    intro x hx
    exact ((eqOn_iteratedFDeriv_of_isOpen (hU i) hlimit m) (hKU hx)).symm
  · intro R hR
    obtain ⟨l, hl⟩ := hboundary R hR
    exact ⟨l, hl.mono fun j hj q hq => by simpa only [hdist] using hj q hq⟩

end PoincareConjecture.ChartDistance

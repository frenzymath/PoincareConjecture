import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.MetricConvergence
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.SourceExhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Metric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChosenChart
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28

theorem exists_regular_metric_limit_of_coordinate_limits
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    [Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    (hstep : ∀ j, 4 * δ (j + 1) ≤ 2 * δ j)
    (hcofinal : ∀ ε : ℝ, 0 < ε → ∃ j, 4 * δ j ≤ ε)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {D : ∀ _i _j : ℕ, C(ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      ball (0 : EuclideanSpace ℝ (Fin n)) 1, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
        ball (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        dist (regularUnitBallMap cover (φ k) i x.1)
          (regularUnitBallMap cover (φ k) j x.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (regularUnitBallMap cover (φ k) i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤
      dist (regularUnitBallMap cover (φ k) i x) (regularUnitBallMap cover (φ k) i y))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' ChartDistance.overlap (fun i j => D i j) i j)
      (fun k => ChartDistance.coordinateRepresentative (fun _ : ℕ => ball 0 1)
        (fun _ => isOpen_ball) (i := i) (j := j)
          (fun x => Function.invFun (regularUnitBallMap cover (φ k) j)
            (regularUnitBallMap cover (φ k) i x))))
    (B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (ball 0 1))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
        ((g (φ k)).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover (φ k) i))))
        (iteratedFDeriv ℝ m (B i)) atTop K)
    (hpositive : ∀ i x, x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ v, a * ‖v‖ ^ 2 ≤
        (g (φ k)).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover (φ k) i)) x v v) :
    Nonempty (RegularPointedMetricConvergence g p) := by
  let U : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun _ => ball 0 1
  let hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hopen := fun k i => regularUnitBallMap_isOpenEmbedding cover hρ hρR (φ k) i
  have hsmooth := fun k i => regularUnitBallMap_isLocalDiffeomorph cover hρ hρR (φ k) i
  have hp := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := ChartDistance.overlapSystem hp L he c hc hlower hopen (fun k => hconn (φ k))
  have hO := ChartDistance.overlapSystem_smooth U hU hp L he c hc hlower
    hopen (fun k => hconn (φ k)) hsmooth hbound
  have hclosed := ChartDistance.overlapSystem_closed hp L he c hc hlower
    hopen (fun k => hconn (φ k))
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ,
      F, hF, happrox, hreadout, hcapture⟩ :=
    exists_regular_pointed_source_exhaustion cover hρ hρR hstep hφ hD L he c hc
      hlower hconn hbound
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have hBlocal (i : ℕ) : TendstoLocallyUniformlyOn
      (fun k => (g (φ k)).pullbackCoefficients
        (ChartDistance.chartParametrization U hU (regularUnitBallMap cover (φ k) i)))
      (B i) atTop (U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hU i) (hBjets i 0)
  obtain ⟨gLimit, hcoeff, hcompat⟩ :=
    ChartDistance.exists_compatibleMetrics_of_coordinate_limits U hU hp L he c hc
      hlower hopen (fun k => hconn (φ k)) hsmooth (fun k => g (φ k)) B hBlocal
      hBsmooth hpositive hbound
  let C := O.flowCarrier U hU hO hclosed
  let gQ := quotientMetric U hU O hO gLimit hcompat
  have hsourceJets := ChartDistance.source_exhaustion_pullbackCoefficients_tendsto_jets
    U hU O hO hE hEmono hEcover F (fun k => (hF k).2.1)
    L (fun k => he (σ k)) c hc (fun k => hlower (σ k))
    (fun k => hopen (σ k)) (fun k => hconn (φ (σ k))) (fun k => hsmooth (σ k))
    happrox hreadout (fun k => g (φ (σ k))) B hBsmooth
    (fun i m K hK hKU V hV => hσ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
  refine ⟨{
    limitCarrier := C
    limitMetric := gQ
    base := O.include 0 ⟨0, by simp⟩
    subsequence := φ ∘ σ
    subsequence_strictMono := hφ.comp hσ
    exhaustion := E
    exhaustion_open := hE
    exhaustion_connected := hEc
    base_in_exhaustion := hEp
    exhaustion_compactClosure := hEK
    exhaustion_step := hEstep
    exhaustion_covers := hEcover
    embedding := F
    embedding_open := fun k => (hF k).1
    embedding_smooth := fun k => (hF k).2.1
    base_preserving := fun k => (hF k).2.2
    metric_jets := ?_
    regular_component_coverage := ?_ }⟩
  · intro q m K hK hKchart
    obtain ⟨i, _, htarget, hinverse⟩ := ChartDistance.exists_chosen_quotient_chart U hU O q
    have hKU : K ⊆ U i := by simpa only [htarget] using hKchart
    rw [hinverse]
    have hlimit : EqOn
        (gQ.pullbackCoefficients (ChartDistance.chartParametrization U hU (O.include i)))
        (B i) (U i) :=
      ChartDistance.quotientMetric_pullbackCoefficients_eqOn
        U hU O hO gLimit hcompat B hcoeff i
    apply (hsourceJets i m K hK hKU).congr_right
    intro x hx
    exact ((eqOn_iteratedFDeriv_of_isOpen (hU i) hlimit m) (hKU hx)).symm
  · intro ε hε
    obtain ⟨j, hj⟩ := hcofinal ε hε
    refine ⟨j, (hcapture j).mono fun k hk => ⟨hk.1, ?_⟩⟩
    exact (regularComponent_antitone (g (φ (σ k))) (p (φ (σ k))) hj).trans hk.2

end PoincareConjecture.M28

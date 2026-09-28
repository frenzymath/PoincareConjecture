import PoincareConjecture.Proofs.M47.TerminalGermsAtlas
import PoincareConjecture.Proofs.M47.TerminalGermsCompleteness
import PoincareConjecture.Proofs.M47.TerminalGermsMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.PointedExhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M47

open ChartDistance

private def ClosedNested {X : Type*} [TopologicalSpace X] (E : ℕ → Set X) : Prop :=
  ∀ j, closure (E j) ⊆ E (j + 1)

private def Covers {X : Type*} (E : ℕ → Set X) : Prop := (⋃ j, E j) = univ

private theorem pointwise_chart_distance
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 3))}
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop) :
    ∀ (i j : ℕ) (x : Piece U i) (y : Piece U j),
      Tendsto (fun k => dist (e k i x) (e k j y)) atTop (𝓝 (D i j (x, y))) := by
  intro i j x y
  exact (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))




theorem terminalGerms_complete_terminal_geometry
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (g : ∀ k, RiemannianMetric 3 (M k))
    (hactual : ∀ (k : ℕ) (x y : M k), edist x y = (g k).edist x y)
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k i))
    (hjets : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i))))
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤
          (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    {i₀ : ℕ} (p : Piece U i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (B : ℕ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (U i))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((g k).pullbackCoefficients (chartParametrization U hU (e k i))))
      (iteratedFDeriv ℝ m (B i)) atTop K) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let hpoint := pointwise_chart_distance hD
    let O := overlapSystem hpoint L he c hc hlower hopen hconn
    ∃ hO : SmoothOverlap U hU O,
      ConnectedSpace (Quotient O.setoid) ∧
      letI : T2Space (Quotient O.setoid) :=
        O.quotient_t2Space (overlapSystem_closed hpoint L he c hc hlower hopen hconn)
      letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      letI : LocallyCompactSpace (Quotient O.setoid) :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
      ∃ gQ : RiemannianMetric 3 (Quotient O.setoid), MetricComplete gQ ∧
        (∀ i (x : Piece U i) (v w : TangentSpace (𝓡 3) x),
          B i x v w = gQ.inner (O.include i x)
            (mfderiv (𝓡 3) (𝓡 3) (O.include i) x v)
            (mfderiv (𝓡 3) (𝓡 3) (O.include i) x w)) ∧
        ∃ E : ℕ → Set (Quotient O.setoid),
          (∀ j, IsOpen (E j)) ∧ (∀ j, IsConnected (E j)) ∧
          (∀ j, O.include i₀ p ∈ E j) ∧ (∀ j, IsCompact (closure (E j))) ∧
          ClosedNested E ∧ Covers E ∧
        ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ f : ∀ k, Quotient O.setoid → M (sigma k),
          (∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x) ∧
            IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k) ∧
            f k (O.include i₀ p) = e (sigma k) i₀ p) ∧
          (∀ (i : ℕ) (K : Set (Piece U i)), IsCompact K → TendstoUniformlyOn
            (fun (k : ℕ) (x : Piece U i) =>
              dist (f k (O.include i x)) (e (sigma k) i x)) (fun _ => 0) atTop K) ∧
          (∀ (i m : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))),
            IsCompact K → K ⊆ U i → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m
              ((g (sigma k)).pullbackCoefficients
                (chartParametrization U hU (f k ∘ O.include i))))
            (iteratedFDeriv ℝ m (B i)) atTop K) ∧
          ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
            ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤
              (g (sigma k)).edist (f k (O.include i₀ p)) (f k x) := by
  classical
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let hp := pointwise_chart_distance hD
  let O := overlapSystem hp L he c hc hlower hopen hconn
  have hBlocal (i : ℕ) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hU i) (hBjets i 0)
  obtain ⟨hT2, hSecond, hO, gLimit, hcompat, hcoeff, hmetric⟩ :=
    terminalGerms_terminal_atlas U hU hp L he c hc hlower hopen hconn hsmooth g
      hjets helliptic B hBlocal hBsmooth
  let : T2Space (Quotient O.setoid) := hT2
  let : SecondCountableTopology (Quotient O.setoid) := hSecond
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  let : LocallyCompactSpace (Quotient O.setoid) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  have htransition := fun i j => locallyEventuallyBoundedDerivatives_source_transition
    U hU hp L he c hc hlower hopen hconn hsmooth g hjets helliptic i j
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, sigma, hsigma,
      f, hf, happrox, hreadout, hescape⟩ :=
    exists_pointed_source_exhaustion_with_boundary_escape U hU hD L he c hc hlower
      hopen hconn hsmooth htransition p hcover
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have hsourceJets := source_exhaustion_pullbackCoefficients_tendsto_jets U hU O hO
    hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (sigma k)) c hc (fun k => hlower (sigma k))
    (fun k => hopen (sigma k)) (fun k => hconn (sigma k))
    (fun k => hsmooth (sigma k)) happrox hreadout (fun k => g (sigma k)) B hBsmooth
    (fun i m K hK hKU V hV => hsigma.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
  have hsourceZero : ∀ i K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => (g (sigma k)).pullbackCoefficients
        (chartParametrization U hU (f k ∘ O.include i))) (B i) atTop K := by
    intro i K hK hKU
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn
          (hsourceJets i 0 K hK hKU)
  have hquad := terminalGerms_source_quadratic_bound U hU O hO E hE hEmono hEcover f
    (fun k => (hf k).2.1) (fun k => g (sigma k)) gLimit hcompat B
    (fun i => (hBsmooth i).continuousOn) hcoeff hsourceZero
  have hescapeActual : ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤
        (g (sigma k)).edist (f k (O.include i₀ p)) (f k x) := by
    intro A hA
    obtain ⟨j, hj⟩ := hescape A hA
    refine ⟨j, hj.mono fun k hk x hx => ?_⟩
    rw [(hf k).2.2, ← hactual (sigma k)]
    exact hk x hx
  let gQ := quotientMetric U hU O hO gLimit hcompat
  have hcomplete : MetricComplete gQ := terminalGerms_metricComplete_of_boundary_escape
    gQ (fun k => g (sigma k)) E hE hEK hEstep hEmono hEcover (O.include i₀ p) hEp
    f (fun k => (hf k).1) (fun k => (hf k).2.1) hquad hescapeActual
  exact ⟨hO, hconnected, gQ, hcomplete, hmetric,
    E, hE, hEc, hEp, hEK, hEstep, hEcover, sigma, hsigma, f, hf,
    happrox, hsourceJets, hescapeActual⟩

end PoincareConjecture.M47

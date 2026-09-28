import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Assembly
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Complete
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.RicciFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.PointedExhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.SpacetimeMetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Subsequence















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {n : ℕ} {T' T : ℝ} (S : PointedFlowSequence n T' T)

local instance (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance (k : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold
local instance (k : ℕ) : MetricSpace (S.carrier k).carrier :=
  (S.carrier k).metricSpaceOf ((S.flow k).metricAt 0)





theorem exists_complete_geometric_limit_of_chart_limits
    (hT : T' < 0 ∧ 0 < T)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (e : ∀ k i, Piece U i → (S.carrier k).carrier)
    (D : ∀ i j, C(Piece U i × Piece U j, ℝ))
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {i₀ : ℕ} (p : Piece U i₀) (hbase : ∀ k, e k i₀ p = (S.flow k).base)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (B : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Ioo T' T ×ˢ U i))
    (hBjets : ∀ i m K, IsCompact K → K ⊆ Ioo T' T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hpositive : ∀ t ∈ Ioo T' T, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ G : PointedGeometricConvergence S,
      G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) := by
  classical
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hconn : ∀ k (q : (S.carrier k).carrier) r, IsPreconnected (ball q r) := by
    intro k q r
    rw [FlowCarrier.metricBall_eq_metricBallOf]
    exact ((S.flow k).metricAt 0).isPreconnected_ball q r
  let hp := fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hp L he c hc hlower hopen hconn hsmooth hbound
  let hclosed := overlapSystem_closed hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ,
      f, hf, happrox, hreadout, hescape⟩ :=
    exists_pointed_source_exhaustion_with_boundary_escape U hU hD L he c hc hlower
      hopen hconn hsmooth hbound p hcover
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have hBlocal (i : ℕ) : TendstoLocallyUniformlyOn
      (fun k z => ((S.flow k).flow.metric z.1).pullbackCoefficients
        (chartParametrization U hU (e k i)) z.2)
      (B i) atTop (Ioo T' T ×ˢ U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (isOpen_Ioo.prod (hU i)) (hBjets i 0)
  have hBslice : ∀ t ∈ Ioo T' T, ∀ i, TendstoLocallyUniformlyOn
      (fun k => ((S.flow k).flow.metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)))
      (fun x => B i (t, x)) atTop (U i) := by
    intro t ht i
    exact (hBlocal i).comp (fun x => (t, x)) (fun _ hx => ⟨ht, hx⟩)
      (continuous_const.prodMk continuous_id).continuousOn
  obtain ⟨gLimit, hcompat, hcoeff, hfamily, _⟩ :=
    exists_compatibleMetricFamilies_of_spacetime_limits U hU hp L he c hc hlower
      hopen hconn hsmooth 0 hT (fun k => (S.flow k).flow.metric) B hBslice
      hBsmooth hpositive hbound
  have hlocal : ∀ i, ∃ F : RicciFlow n (Piece U i) (Ioo T' T),
      F.metric = fun t => gLimit t i := by
    intro i
    exact exists_ricciFlow_on_coordinate_limit U hU isOpen_Ioo
      (fun k => (S.flow k).flow) i (fun k => e k i) (fun k => hsmooth k i)
      (fun t => gLimit t i) (hfamily i) (B i) (fun t ht => hcoeff t ht i) (hBjets i)
  choose Fchart hFchart using hlocal
  obtain ⟨FQ, hFQ⟩ := exists_quotientRicciFlow_of_chart_flows U hU O hO
    gLimit hcompat Fchart hFchart
  let C := O.flowCarrier U hU hO hclosed
  let F : BasedFlow n T' T C :=
    { base := O.include i₀ p
      flow := FQ
      volumeMeasure := C.metricHausdorffVolume (FQ.metric 0)
      spacetimeVectorField := fun _ _ => (1, 0)
      spacetimeVectorField_time := fun _ _ => rfl
      spacetimeVectorField_spatial_zero := fun _ _ => rfl }
  have hsourceJets := source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets_of_smooth_families
    U hU O hO hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (σ k)) c hc (fun k => hlower (σ k))
    (fun k => hopen (σ k)) (fun k => hconn (σ k)) (fun k => hsmooth (σ k))
    happrox hreadout (Ioo T' T) isOpen_Ioo
    (fun k => (S.flow (σ k)).flow.metric) (fun k => (S.flow (σ k)).flow.smooth)
    B hBsmooth (fun i m K hK hKU u hu =>
      hσ.tendsto_atTop.eventually (hBjets i m K hK hKU u hu))
  let G₀ := pointedGeometricConvergence_of_quotient_limit U hU O hO hclosed
    (fun k => S.flow (σ k)) F gLimit hcompat hFQ hE hEc hEK hEmono hEcover
    f (fun k => (hf k).1) (fun k => (hf k).2.1) hEp
    (fun k => (hf k).2.2.trans (hbase (σ k))) B
    (fun i => (hBsmooth i).continuousOn) hcoeff hsourceJets
  let G : PointedGeometricConvergence S := G₀.ofSubsequence hσ
  refine ⟨G, G.metricComplete_zero_of_boundary_escape hT ?_⟩
  intro A hA
  obtain ⟨j, hj⟩ := hescape A hA
  refine ⟨j, hj.mono fun k hk x hx => ?_⟩
  have hx' := hk x hx
  rw [hbase (σ k)] at hx'
  exact hx'




theorem exists_complete_geometric_limit_of_controlled_charts
    (hT : T' < 0 ∧ 0 < T)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (e : ∀ k i, Piece U i → (S.carrier k).carrier)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hb : ∀ i j (x : Piece U i) (y : Piece U j), ∃ C : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ C)
    {i₀ : ℕ} (p : Piece U i₀) (hbase : ∀ k, e k i₀ p = (S.flow k).base)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric 0).pullbackCoefficients
          (chartParametrization U hU (e k i)) x v v)
    (hjets : ∀ i K, IsCompact K → K ⊆ Ioo T' T ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow k).flow.metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2) z‖ ≤ C)
    (hpositive : ∀ t ∈ Ioo T' T, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ G : PointedGeometricConvergence S,
      G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hsource (i k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) z.2) (Ioo T' T ×ˢ U i) :=
    contDiffOn_source_chart_spacetime_pullbackCoefficients U hU
      (hsmooth k i).contMDiff (S.flow k).flow.smooth isOpen_Ioo
  have hzerojets (i : ℕ) : LocallyEventuallyBoundedDerivatives (U i)
      (fun k => ((S.flow k).flow.metric 0).pullbackCoefficients
        (chartParametrization U hU (e k i))) :=
    locallyEventuallyBoundedDerivatives_comp_continuousLinearMap
      (U := Ioo T' T ×ˢ U i) (Ω := U i)
      (f := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) z.2)
      ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))
      (isOpen_Ioo.prod (hU i)) (fun _ hx => ⟨hT, hx⟩) (hsource i) (hjets i)
  obtain ⟨σ, hσ, B, hBsmooth, hBjets⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ => ℝ × EuclideanSpace ℝ (Fin n))
      (F := fun _ => EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (Ω := fun i => Ioo T' T ×ˢ U i)
      (fun i => isOpen_Ioo.prod (hU i))
      (fun i k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
        (chartParametrization U hU (e k i)) z.2) hsource hjets
  obtain ⟨τ, hτ, D, hD⟩ := exists_pairwise_limits (fun k => e (σ k)) L
    (fun k => he (σ k)) (fun i j x y => by
      obtain ⟨C, hC⟩ := hb i j x y
      exact ⟨C, fun k => hC (σ k)⟩)
  let ρ := σ ∘ τ
  have hρ : StrictMono ρ := hσ.comp hτ
  have hconn : ∀ k (q : (S.carrier (ρ k)).carrier) r, IsPreconnected (ball q r) := by
    intro k q r
    rw [FlowCarrier.metricBall_eq_metricBallOf]
    exact ((S.flow (ρ k)).metricAt 0).isPreconnected_ball q r
  have hzerojets' : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => ((S.flow (ρ k)).flow.metric 0).pullbackCoefficients
        (chartParametrization U hU (e (ρ k) i))) := by
    intro i K hK hKU m
    obtain ⟨C, hC⟩ := hzerojets i K hK hKU m
    exact ⟨C, hρ.tendsto_atTop.eventually hC⟩
  have helliptic' : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((S.flow (ρ k)).flow.metric 0).pullbackCoefficients
          (chartParametrization U hU (e (ρ k) i)) x v v := by
    intro i K hK hKU
    obtain ⟨a, ha, hbound⟩ := helliptic i K hK hKU
    exact ⟨a, ha, hρ.tendsto_atTop.eventually hbound⟩
  have hbound := locallyEventuallyBoundedDerivatives_source_transition U hU
    (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k => he (ρ k)) c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k))
    hconn (fun k => hsmooth (ρ k)) (fun k => (S.flow (ρ k)).flow.metric 0)
    hzerojets' helliptic'
  have hcover' : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e (ρ k) i₀ p) R ⊆ ⋃ i ∈ s, e (ρ k) i '' K i := by
    intro R hR
    obtain ⟨s, K, hK, hcover⟩ := hcover R hR
    exact ⟨s, K, hK, hρ.tendsto_atTop.eventually hcover⟩
  have hpositive' : ∀ t ∈ Ioo T' T, ∀ i x, x ∈ U i → ∃ a : ℝ,
      0 < a ∧ ∀ᶠ k in atTop, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((S.flow (ρ k)).flow.metric t).pullbackCoefficients
          (chartParametrization U hU (e (ρ k) i)) x v v := by
    intro t ht i x hx
    obtain ⟨a, ha, hpos⟩ := hpositive t ht i x hx
    exact ⟨a, ha, hρ.tendsto_atTop.eventually hpos⟩
  obtain ⟨G, hcomplete⟩ := exists_complete_geometric_limit_of_chart_limits
    (S.subsequence ρ) hT U hU (fun k => e (ρ k)) D hD L (fun k => he (ρ k))
    c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k)) (fun k => hsmooth (ρ k))
    hbound p (fun k => hbase (ρ k)) hcover' B hBsmooth
    (fun i m K hK hKU u hu => hτ.tendsto_atTop.eventually (hBjets i m K hK hKU u hu))
    hpositive'
  exact ⟨G.ofSubsequence hρ, hcomplete⟩

end PoincareConjecture.ChartDistance

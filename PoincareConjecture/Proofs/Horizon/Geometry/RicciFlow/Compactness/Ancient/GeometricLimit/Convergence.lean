import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.RicciFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Window
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.SpacetimeMetricConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets_of_expanding_flows
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (f : ∀ k, Quotient O.setoid → M k)
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    {e : ∀ k i, Piece U i → M k}
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (happrox : ∀ i C, IsCompact C → TendstoUniformlyOn
      (fun k x => dist (f k (O.include i x)) (e k i x)) (fun _ => 0) atTop C)
    (hreadout : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (coordinateRepresentative U hU
          (fun x => Function.invFun (e k i) (f k (O.include i x)))))
      (iteratedFDeriv ℝ m id) atTop K)
    {T : ℝ} {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (Iio T ×ˢ U i))
    (hBjet : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => ((Fseq k).metric y.1).pullbackCoefficients
          (chartParametrization U hU (e k i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K) :
    ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => ((Fseq k).metric y.1).pullbackCoefficients
          (chartParametrization U hU (f k ∘ O.include i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K := by
  apply source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets U hU O hO
    hE hEmono hEcover f hf L he c hc hlower hopen hconn hsmooth happrox hreadout
    (Iio T) isOpen_Iio (fun k ↦ (Fseq k).metric) B hB ?_ hBjet
  intro i z hz
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hzT : z.1 < T := hz.1
  let a := z.1 - 1
  let b := (z.1 + T) / 2
  have ha : a < z.1 := by dsimp [a]; linarith
  have hzb : z.1 < b := by dsimp [b]; linarith
  have hb : b < T := by dsimp [b]; linarith
  refine ⟨Ioo a b ×ˢ U i, isOpen_Ioo.prod (hU i), ⟨⟨ha, hzb⟩, hz.2⟩, ?_⟩
  filter_upwards [htime a b hb] with k hk
  exact contDiffOn_source_chart_spacetime_pullbackCoefficients U hU
    (hsmooth k i).contMDiff ((Fseq k).smooth.mono
      (prod_mono (Ioo_subset_Icc_self.trans hk) (Subset.refl _))) isOpen_Ioo

section FiniteWindow

variable {n : ℕ} (D : ℕ → FlowCarrier n)

local instance ancientConvergence_sourceTopology (k : ℕ) :
    TopologicalSpace (D k).carrier := (D k).topologicalSpace
local instance ancientConvergence_sourceCharts (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
  (D k).chartedSpace
local instance ancientConvergence_sourceManifold (k : ℕ) :
    IsManifold (𝓡 n) ∞ (D k).carrier := (D k).isManifold

noncomputable def completeAncientWindowConvergence
    {ι : Type} [Countable ι]
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    (hclosed : ∀ i j, IsClosed {q : Piece U i × Piece U j |
      O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})
    [ConnectedSpace (Quotient O.setoid)]
    {T a b : ℝ} (hwindow : a < 0 ∧ 0 < b) (hb : b ≤ T)
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (D k).carrier (J k))
    (p : ∀ k, (D k).carrier)
    (N : ℕ) (hsub : ∀ k, Ioo a b ⊆ J (k + N))
    (F : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      RicciFlow n (Quotient O.setoid) (Iio T))
    (q : Quotient O.setoid)
    (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t))
    (hF : letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      F.metric = fun t => quotientMetric U hU O hO (gLimit t) (hcompat t))
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEc : ∀ k, IsConnected (E k))
    (hEK : ∀ k, IsCompact (closure (E k)))
    (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    (f : ∀ k, Quotient O.setoid → (D k).carrier)
    (hemb : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    (hbase : ∀ k, q ∈ E k) (hbase_preserving : ∀ k, f k q = p k)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hBcont : ∀ i, ContinuousOn (B i) (Iio T ×ˢ U i))
    (hB : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ Iio T, ∀ i (x : Piece U i) v w,
        (gLimit t i).inner x v w = B i (t, x) v w)
    (hjets : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (f k ∘ O.include i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤
        ((D k).metricEMetricSpace ((Fseq k).metric 0)).edist (p k) (f k x)) :
    {G : PointedGeometricConvergence
        (sourceWindowSequence D Fseq p N hsub (hwindow.1.trans hwindow.2)) //
      G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)} := by
  let C := O.flowCarrier U hU hO hclosed
  letI := quotientChartedSpace U hU O
  letI := quotient_isManifold U hU O hO
  let Fwindow : BasedFlow n a b C :=
    C.basedWindow F q (fun _ ht ↦ ht.2.trans_le hb) (hwindow.1.trans hwindow.2)
  let S := sourceWindowSequence D Fseq p N hsub (hwindow.1.trans hwindow.2)
  have hem : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f (k + N) x) := by
    intro k
    exact (hemb (k + N)).comp (Topology.IsOpenEmbedding.inclusion
      (hEmono (by omega : k ≤ k + N)) ((hE k).preimage continuous_subtype_val))
  have hfm : ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f (k + N)) (E k) :=
    fun k x ↦ hf (k + N) ⟨x, hEmono (by omega : k ≤ k + N) x.property⟩
  have hwin : Ioo a b ⊆ Iio T := fun _ ht ↦ ht.2.trans_le hb
  let G := pointedGeometricConvergence_of_quotient_limit U hU O hO hclosed
    S.flow Fwindow gLimit hcompat hF hE hEc hEK hEmono hEcover
    (fun k ↦ f (k + N)) hem hfm hbase (fun k ↦ hbase_preserving (k + N)) B
    (fun i ↦ (hBcont i).mono (prod_mono hwin (Subset.refl _)))
    (fun t ht ↦ hB t (hwin ht))
    (fun i m K hK hKU V hV ↦ (tendsto_add_atTop_nat N).eventually
      (hjets i m K hK (hKU.trans (prod_mono hwin (Subset.refl _))) V hV))
  refine ⟨G, G.metricComplete_zero_of_boundary_escape hwindow ?_⟩
  intro A hA
  obtain ⟨j, hj⟩ := hescape A hA
  exact ⟨j, (tendsto_add_atTop_nat N).eventually hj⟩

end FiniteWindow

end PoincareConjecture.ChartDistance

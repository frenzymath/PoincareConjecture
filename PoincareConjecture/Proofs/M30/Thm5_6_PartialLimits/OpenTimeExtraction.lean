import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.OpenTimeQuotientFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.SpacetimeMetricConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open PoincareConjecture.ChartDistance
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M30

theorem exists_quotientFlow_of_controlled_charts_on_open_time
    {n : ℕ}
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (e : ∀ k i, Piece U i → M k)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hb : ∀ i j (x : Piece U i) (y : Piece U j), ∃ C : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ C)
    {W : Set ℝ} (hW : IsOpen W) (hWord : Set.OrdConnected W)
    (hzero : (0 : ℝ) ∈ W)
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq k).metric 0).pullbackCoefficients
          (chartParametrization U hU (e k i)) x v v)
    (hjets : ∀ i K, IsCompact K → K ⊆ W ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2) z‖ ≤ C)
    (hpositive : ∀ t ∈ W, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ (σ : ℕ → ℕ) (_hσ : StrictMono σ)
      (B : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (_hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (W ×ˢ U i))
      (_hBjets : ∀ i m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq (σ k)).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e (σ k) i)) z.2))
        (iteratedFDeriv ℝ m (B i)) atTop K)
      (D : ∀ i j, C(Piece U i × Piece U j, ℝ))
      (hD : ∀ i j, TendstoLocallyUniformly
        (fun k (p : Piece U i × Piece U j) =>
          dist (e (σ k) i p.1) (e (σ k) j p.2)) (D i j) atTop)
      (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
        (Subtype.val '' overlap (fun i j => D i j) i j)
        (fun k => coordinateRepresentative U hU
          (fun x => Function.invFun (e (σ k) j) (e (σ k) i x)))),
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let hp := fun i j x y =>
      (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
    let O := overlapSystem hp L (fun k => he (σ k)) c hc
      (fun k => hlower (σ k)) (fun k => hopen (σ k)) (fun k => hconn (σ k))
    let hO := overlapSystem_smooth U hU hp L (fun k => he (σ k)) c hc
      (fun k => hlower (σ k)) (fun k => hopen (σ k)) (fun k => hconn (σ k))
      (fun k => hsmooth (σ k)) hbound
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
            ((Fseq (σ k)).metric z.1).pullbackCoefficients
              (chartParametrization U hU (e (σ k) i)) z.2))
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
  let A (i k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin n)) :=
    ((Fseq k).metric z.1).pullbackCoefficients (chartParametrization U hU (e k i)) z.2
  have hsource (i : ℕ) : LocallyEventuallyContDiff (W ×ˢ U i) (A i) := by
    apply locallyEventuallyContDiff_of_local
    intro z hz
    obtain ⟨a, b, _, habnhds, habW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds hz.1)
    have hab : z.1 ∈ Ioo a b := Icc_mem_nhds_iff.mp habnhds
    refine ⟨Ioo a b ×ˢ U i, isOpen_Ioo.prod (hU i), ⟨hab, hz.2⟩, ?_⟩
    filter_upwards [htime a b habW] with k hk
    exact contDiffOn_source_chart_spacetime_pullbackCoefficients U hU
      (hsmooth k i).contMDiff
      ((Fseq k).smooth.mono (prod_mono (Ioo_subset_Icc_self.trans hk) (Subset.refl _)))
      isOpen_Ioo
  have hzerojets (i : ℕ) : LocallyEventuallyBoundedDerivatives (U i)
      (fun k => ((Fseq k).metric 0).pullbackCoefficients
        (chartParametrization U hU (e k i))) := by
    let Z : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n) :=
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    intro K hK hKU m
    have hZK : IsCompact (Z '' K) := hK.image Z.continuous
    have hZKU : Z '' K ⊆ W ×ˢ U i := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hzero, hKU hx⟩
    obtain ⟨B, hB⟩ := hjets i (Z '' K) hZK hZKU m
    refine ⟨B * ∏ _ : Fin m, ‖Z‖, ?_⟩
    filter_upwards [hB, hsource i (Z '' K) hZK hZKU] with k hk ⟨V, hV, hZV, hfd⟩ x hx
    have hs : ContDiffAt ℝ ∞ (A i k) (Z x) :=
      hfd.contDiffAt (hV.mem_nhds (hZV (mem_image_of_mem Z hx)))
    change ‖iteratedFDeriv ℝ m (A i k ∘ Z) x‖ ≤ _
    rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt Z hs m]
    exact ((iteratedFDeriv ℝ m (A i k) (Z x)).norm_compContinuousLinearMap_le
      (fun _ : Fin m => Z)).trans
        (mul_le_mul_of_nonneg_right (hk (Z x) (mem_image_of_mem Z hx))
          (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  obtain ⟨σ, hσ, B, hBsmooth, hBjets⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      (X := fun _ => ℝ × EuclideanSpace ℝ (Fin n))
      (Y := fun _ => EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (Ω := fun i => W ×ˢ U i)
      (fun i => hW.prod (hU i)) A hsource hjets
  obtain ⟨τ, hτ, D, hD⟩ := exists_pairwise_limits (fun k => e (σ k)) L
    (fun k => he (σ k)) (fun i j x y => by
      obtain ⟨C, hC⟩ := hb i j x y
      exact ⟨C, fun k => hC (σ k)⟩)
  let ρ := σ ∘ τ
  have hρ : StrictMono ρ := hσ.comp hτ
  have hzerojets' : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => ((Fseq (ρ k)).metric 0).pullbackCoefficients
        (chartParametrization U hU (e (ρ k) i))) := by
    intro i K hK hKU m
    obtain ⟨C, hC⟩ := hzerojets i K hK hKU m
    exact ⟨C, hρ.tendsto_atTop.eventually hC⟩
  have helliptic' : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq (ρ k)).metric 0).pullbackCoefficients
          (chartParametrization U hU (e (ρ k) i)) x v v := by
    intro i K hK hKU
    obtain ⟨a, ha, hbound⟩ := helliptic i K hK hKU
    exact ⟨a, ha, hρ.tendsto_atTop.eventually hbound⟩
  have hbound := locallyEventuallyBoundedDerivatives_source_transition U hU
    (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k => he (ρ k)) c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k))
    (fun k => hconn (ρ k)) (fun k => hsmooth (ρ k)) (fun k => (Fseq (ρ k)).metric 0)
    hzerojets' helliptic'
  have hBjets' : ∀ i m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A i (ρ k))) (iteratedFDeriv ℝ m (B i)) atTop K := by
    intro i m K hK hKU V hV
    exact hτ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV)
  refine ⟨ρ, hρ, B, hBsmooth, hBjets', D, hD, hbound, ?_⟩
  apply exists_quotientFlow_of_chart_limits_on_open_time U hU (fun k => e (ρ k)) D
    (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k => he (ρ k)) c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k))
    (fun k => hconn (ρ k)) (fun k => hsmooth (ρ k)) hbound hW hWord hzero
    (fun k => Fseq (ρ k)) (fun a b hab => hρ.tendsto_atTop.eventually (htime a b hab))
    B hBsmooth hBjets'
  intro t ht i x hx
  obtain ⟨a, ha, hpos⟩ := hpositive t ht i x hx
  exact ⟨a, ha, hρ.tendsto_atTop.eventually hpos⟩

end PoincareConjecture.M30

import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.QuotientFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.SpacetimeMetricConvergence














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance




theorem exists_ancient_quotientRicciFlow_of_controlled_charts
    {n : ℕ}
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
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
    {T : ℝ} (hT : 0 < T) {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq k).metric 0).pullbackCoefficients
          (chartParametrization U hU (e k i)) x v v)
    (hjets : ∀ i K, IsCompact K → K ⊆ Iio T ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2) z‖ ≤ C)
    (hpositive : ∀ t ∈ Iio T, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ (σ : ℕ → ℕ) (_hσ : StrictMono σ)
      (B : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (_hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Iio T ×ˢ U i))
      (_hBjets : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
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
      (F : RicciFlow n (Quotient O.setoid) (Iio T)),
      F.metric = (fun t => quotientMetric U hU O hO (g t) (hcompat t)) ∧
      ∀ t ∈ Iio T, ∀ i (x : Piece U i) v w,
        (g t i).inner x v w = B i (t, x) v w := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let A (i k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin n)) :=
    ((Fseq k).metric z.1).pullbackCoefficients (chartParametrization U hU (e k i)) z.2
  have hsource (i : ℕ) : LocallyEventuallyContDiff (Iio T ×ˢ U i) (A i) := by
    apply locallyEventuallyContDiff_of_local
    intro z hz
    have hzT : z.1 < T := hz.1
    let a := z.1 - 1
    let b := (z.1 + T) / 2
    have ha : a < z.1 := by dsimp [a]; linarith
    have hzb : z.1 < b := by dsimp [b]; linarith
    have hb : b < T := by dsimp [b]; linarith
    refine ⟨Ioo a b ×ˢ U i, isOpen_Ioo.prod (hU i), ⟨⟨ha, hzb⟩, hz.2⟩, ?_⟩
    filter_upwards [htime a b hb] with k hk
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
    have hZKU : Z '' K ⊆ Iio T ×ˢ U i := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hT, hKU hx⟩
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
      (Ω := fun i => Iio T ×ˢ U i)
      (fun i => isOpen_Iio.prod (hU i)) A hsource hjets
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
  have hBjets' : ∀ i m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A i (ρ k))) (iteratedFDeriv ℝ m (B i)) atTop K := by
    intro i m K hK hKU V hV
    exact hτ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV)
  refine ⟨ρ, hρ, B, hBsmooth, hBjets', D, hD, hbound, ?_⟩
  apply exists_ancient_quotientRicciFlow_of_chart_limits U hU (fun k => e (ρ k)) D
    (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k => he (ρ k)) c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k))
    (fun k => hconn (ρ k)) (fun k => hsmooth (ρ k)) hbound hT
    (fun k => Fseq (ρ k)) (fun a b hb => hρ.tendsto_atTop.eventually (htime a b hb))
    B hBsmooth hBjets'
  intro t ht i x hx
  obtain ⟨a, ha, hpos⟩ := hpositive t ht i x hx
  exact ⟨a, ha, hρ.tendsto_atTop.eventually hpos⟩

end PoincareConjecture.ChartDistance

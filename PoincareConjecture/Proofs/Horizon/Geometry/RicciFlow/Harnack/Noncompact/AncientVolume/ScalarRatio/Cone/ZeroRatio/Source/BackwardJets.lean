import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.MetricConvergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal ENNReal

private theorem tendstoUniformlyOn_prod_of_parameter_sequences
    {T X Y : Type*} [PseudoMetricSpace Y]
    {S : Set T} {K : Set X} {f : ℕ → T × X → Y} {g : X → Y}
    (h : ∀ τ : ℕ → S, TendstoUniformlyOn
      (fun k x => f k (τ k, x)) g atTop K) :
    TendstoUniformlyOn f (fun z => g z.2) atTop (S ×ˢ K) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨t₀, ht₀⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (by simp [hS])
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let bad (k : ℕ) (t : S) := ∃ x ∈ K, ¬ dist (g x) (f k (t, x)) < ε
  let τ : ℕ → S := fun k =>
    if hb : ∃ t : S, bad k t then hb.choose else ⟨t₀, ht₀⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h τ) ε hε] with k hk
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  by_contra hbad
  have hex : ∃ t : S, bad k t := ⟨⟨t, ht⟩, x, hx, hbad⟩
  have hbτ : bad k (τ k) := by
    dsimp only [τ]
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨y, hy, hfail⟩ := hbτ
  exact hfail (hk y hy)

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_tendsto_jets_uniform_parameter_of_corrected_charts
    {n : ℕ} {T : Type*} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, T → RiemannianMetric n (M k))
    (φ ψ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {S : Set T} {U Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩU : Ω ⊆ U)
    (hφ : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (φ k) U)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hBjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k (z : T × EuclideanSpace ℝ (Fin n)) =>
        iteratedFDeriv ℝ m ((g k z.1).pullbackCoefficients (φ k)) z.2)
      (fun z => iteratedFDeriv ℝ m B z.2) atTop (S ×ˢ K))
    (a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k))
    (hajet : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K)
    (heq : ∀ᶠ k in atTop, EqOn (ψ k) (φ k ∘ a k) Ω) :
    ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k (z : T × EuclideanSpace ℝ (Fin n)) =>
        iteratedFDeriv ℝ m ((g k z.1).pullbackCoefficients (ψ k)) z.2)
      (fun z => iteratedFDeriv ℝ m B z.2) atTop (S ×ˢ K) := by
  intro m K hK hKΩ
  apply tendstoUniformlyOn_prod_of_parameter_sequences
  intro τ
  apply pullbackCoefficients_tendsto_jets_of_corrected_charts
    (fun k => g k (τ k)) φ ψ hU hΩ hΩU hφ B hB ?_ a ha hajet heq m K hK hKΩ
  intro l C hC hCU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hBjet l C hC hCU) ε hε]
    with k hk x hx
  exact hk (τ k, x) ⟨(τ k).property, hx⟩

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.ChartDistance

theorem HasLocalSourceModels.exists_local_pullbackCoefficients_tendsto_jets_uniform_parameter
    {ι : Type*} {n : ℕ} {T : Type*}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (e : ∀ k i, Piece U i → M k)
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, ContMDiff (𝓡 n) (𝓡 n) ∞ (e k i))
    (g : ∀ k, T → RiemannianMetric n (M k)) (S : Set T)
    (B : ι → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (U i))
    (hBjet : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k (z : T × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
        ((g k z.1).pullbackCoefficients (chartParametrization U hU (e k i))) z.2)
      (fun z => iteratedFDeriv ℝ m (B i) z.2) atTop (S ×ˢ K))
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (hmodels : HasLocalSourceModels U hU O e F V) :
    ∀ q ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
      q ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
      ∀ m K, IsCompact K → K ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k (z : T × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
          ((g k z.1).pullbackCoefficients
            (chartParametrization U hU (F k ∘ O.include i))) z.2)
        (fun z => iteratedFDeriv ℝ m (B i) z.2) atTop (S ×ˢ K) := by
  intro q hq
  obtain ⟨i, W, hW, hqW, hWV, a, ha, hajet, hformula⟩ := hmodels q hq
  refine ⟨i, W, hW, hqW, hWV, ?_⟩
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  apply RiemannianMetric.pullbackCoefficients_tendsto_jets_uniform_parameter_of_corrected_charts g
    (fun k => chartParametrization U hU (e k i))
    (fun k => chartParametrization U hU (F k ∘ O.include i))
    (hU i) ((hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hW)
    (by rintro _ ⟨x, _, rfl⟩; exact x.property)
    (fun k => contMDiffOn_chartParametrization U hU (hsmooth k i))
    (B i) (hB i) (hBjet i) a ha hajet
  filter_upwards [hformula] with k hk
  rintro _ ⟨y, hy, rfl⟩
  simpa only [chartParametrization_apply, Function.comp_apply] using hk y hy

end PoincareConjecture.ChartDistance

namespace PoincareConjecture.RiemannianMetric

theorem exists_local_source_metric_convergence_uniform_parameter_of_normal_charts
    {ι : Type*} {n : ℕ} {T : Type*}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, T → RiemannianMetric n (M k)) (S : Set T)
    (Φ : ∀ k, ι → PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (hsource : ∀ k i, U i ⊆ (Φ k i).source)
    (h : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hjets : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k (z : T × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
        ((g k z.1).pullbackCoefficients (Φ k i)) z.2)
      (fun z => iteratedFDeriv ℝ m (h i).euclideanCoefficients z.2) atTop (S ×ˢ K))
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (hmodels : ChartDistance.HasLocalSourceModels U hU O (fun k i x => Φ k i x) F V) :
    ∀ q ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
      q ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
      ∀ m K, IsCompact K → K ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k (z : T × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
          ((g k z.1).pullbackCoefficients
            (ChartDistance.chartParametrization U hU (F k ∘ O.include i))) z.2)
        (fun z => iteratedFDeriv ℝ m (h i).euclideanCoefficients z.2) atTop (S ×ˢ K) := by
  apply ChartDistance.HasLocalSourceModels.exists_local_pullbackCoefficients_tendsto_jets_uniform_parameter
    U hU O (fun k i x => Φ k i x) ?_ g S (fun i => (h i).euclideanCoefficients)
    (fun i x _ => ((h i).contDiffAt_euclideanCoefficients x).contDiffWithinAt) ?_ hmodels
  · let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    intro k i
    exact (isLocalDiffeomorph_normal_chart_restrict (Φ k i) (U i) (hU i)
      (hsource k i)).contMDiff
  · intro i m K hK hKU
    apply (hjets i m K hK hKU).congr
    apply Eventually.of_forall
    rintro k ⟨t, x⟩ ⟨_, hx⟩
    exact ((eqOn_iteratedFDeriv_of_isOpen (hU i)
      (fun y hy => (g k t).pullbackCoefficients_chartParametrization_restrict U hU i
        (Φ k i) hy) m).symm.mono hKU) hx

end PoincareConjecture.RiemannianMetric

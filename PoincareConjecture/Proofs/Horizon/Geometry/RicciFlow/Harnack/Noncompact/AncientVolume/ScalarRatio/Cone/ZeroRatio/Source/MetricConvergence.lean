import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricConvergence









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem pullbackCoefficients_tendsto_jets_of_corrected_charts
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k))
    (φ ψ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {U Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩU : Ω ⊆ U)
    (hφ : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (φ k) U)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hBjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (φ k)))
      (iteratedFDeriv ℝ m B) atTop K)
    (a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k))
    (hajet : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K)
    (heq : ∀ᶠ k in atTop, EqOn (ψ k) (φ k ∘ a k) Ω) :
    ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (ψ k)))
      (iteratedFDeriv ℝ m B) atTop K := by
  have hBlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ ((g k).pullbackCoefficients (φ k)) W := by
    intro x hx
    refine ⟨U, hU, hx, Eventually.of_forall fun k y hy => ?_⟩
    exact ((g k).contDiffAt_pullbackCoefficients
      ((hφ k).contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨_, hPjet⟩ := smooth_convergence_pullback_bilinear_on_open hU hΩ
    hB contDiff_id.contDiffOn (fun _ hx => hΩU hx) hBlocal
    (fun x hx => ⟨Ω, hΩ, hx, ha.mono fun _ hk => hk.contDiffOn⟩)
    hBjet (fun m K hK _ => hajet m K hK)
  have hPjet' : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y =>
        ((g k).pullbackCoefficients (φ k) (a k y)).bilinearComp
          (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)))
      (iteratedFDeriv ℝ m B) atTop K := by
    simpa only [id_eq, fderiv_id, ContinuousLinearMap.bilinearComp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.flip_flip] using hPjet
  intro m K hK hKΩ
  apply tendstoUniformlyOn_iteratedFDeriv_of_local_models hΩ ?_ m hK hKΩ
  intro x hx
  obtain ⟨C, hC, hxC, hCΩ⟩ := exists_compact_between isCompact_singleton hΩ
    (singleton_subset_iff.mpr hx)
  have hzero : TendstoUniformlyOn a id atTop C := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn (hajet 0 C hC)
  obtain ⟨T, _, hTU, hmap⟩ := exists_compact_target_of_tendstoUniformlyOn hC hU
    continuous_id.continuousOn (fun _ hy => hΩU (hCΩ hy)) hzero
  refine ⟨interior C, isOpen_interior, hxC (mem_singleton x),
    interior_subset.trans hCΩ,
    (fun k y => ((g k).pullbackCoefficients (φ k) (a k y)).bilinearComp
      (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)), B, ?_, fun _ _ => rfl, ?_⟩
  · filter_upwards [ha, heq, hmap] with k hka hke hkm y hy
    have hnear : ψ k =ᶠ[𝓝 y] φ k ∘ a k :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds (hCΩ (interior_subset hy)), hke⟩
    have hd := mfderiv_comp y
      (((hφ k).contMDiffAt (hU.mem_nhds (hTU (hkm (interior_subset hy))))).mdifferentiableAt
        (by simp)) (hka.differentiable (by simp) y).mdifferentiableAt
    rw [← hnear.mfderiv_eq, mfderiv_eq_fderiv] at hd
    ext v w
    change (g k).inner (ψ k y) (mfderiv (𝓡 n) (𝓡 n) (ψ k) y v)
      (mfderiv (𝓡 n) (𝓡 n) (ψ k) y w) =
      (g k).inner (φ k (a k y))
        (mfderiv (𝓡 n) (𝓡 n) (φ k) (a k y) (fderiv ℝ (a k) y v))
        (mfderiv (𝓡 n) (𝓡 n) (φ k) (a k y) (fderiv ℝ (a k) y w))
    rw [hd, hnear.self_of_nhds]
    rfl
  · intro l C' hC' hC'W
    exact hPjet' l C' hC' (hC'W.trans (interior_subset.trans hCΩ))

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.ChartDistance





theorem HasLocalSourceModels.exists_local_pullbackCoefficients_tendsto_jets
    {ι : Type*} {n : ℕ}
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
    (g : ∀ k, RiemannianMetric n (M k))
    (B : ι → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (U i))
    (hBjet : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((g k).pullbackCoefficients (chartParametrization U hU (e k i))))
      (iteratedFDeriv ℝ m (B i)) atTop K)
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (hmodels : HasLocalSourceModels U hU O e F V) :
    ∀ q ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
      q ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
      ∀ m K, IsCompact K → K ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          ((g k).pullbackCoefficients (chartParametrization U hU (F k ∘ O.include i))))
        (iteratedFDeriv ℝ m (B i)) atTop K := by
  intro q hq
  obtain ⟨i, W, hW, hqW, hWV, a, ha, hajet, hformula⟩ := hmodels q hq
  refine ⟨i, W, hW, hqW, hWV, ?_⟩
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  apply RiemannianMetric.pullbackCoefficients_tendsto_jets_of_corrected_charts g
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





theorem exists_local_source_metric_convergence_of_normal_charts
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k))
    (Φ : ∀ k, ι → PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (hsource : ∀ k i, U i ⊆ (Φ k i).source)
    (h : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hjets : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (Φ k i)))
      (iteratedFDeriv ℝ m (h i).euclideanCoefficients) atTop K)
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (hmodels : ChartDistance.HasLocalSourceModels U hU O (fun k i x => Φ k i x) F V) :
    ∀ q ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
      q ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
      ∀ m K, IsCompact K → K ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (F k ∘ O.include i))))
        (iteratedFDeriv ℝ m (h i).euclideanCoefficients) atTop K := by
  apply ChartDistance.HasLocalSourceModels.exists_local_pullbackCoefficients_tendsto_jets
    U hU O (fun k i x => Φ k i x) ?_ g (fun i => (h i).euclideanCoefficients)
    (fun i x _ => ((h i).contDiffAt_euclideanCoefficients x).contDiffWithinAt) ?_ hmodels
  · let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    intro k i
    exact (isLocalDiffeomorph_normal_chart_restrict (Φ k i) (U i) (hU i)
      (hsource k i)).contMDiff
  · intro i m K hK hKU
    apply (hjets i m K hK hKU).congr
    apply Eventually.of_forall
    intro k
    exact (eqOn_iteratedFDeriv_of_isOpen (hU i)
      (fun x hx => (g k).pullbackCoefficients_chartParametrization_restrict U hU i
        (Φ k i) hx) m).symm.mono hKU

end PoincareConjecture.RiemannianMetric

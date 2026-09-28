import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricIdentity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.ChartContainment
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Pullback
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence











set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {i : ι} {e : ∀ k, Piece U i → M k}
    {f : ∀ k, EuclideanSpace ℝ (Fin n) → M k}
    {L : ℝ≥0} (he : ∀ k, LipschitzWith L (e k))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ k x y, c * dist x y ≤ dist (e k x) (e k y))
    (hopen : ∀ k, Topology.IsOpenEmbedding (e k))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (happrox : ∀ C, IsCompact C → TendstoUniformlyOn
      (fun k (x : Piece U i) => dist (f k x) (e k x)) (fun _ => 0) atTop C)
    (hflocal : ∀ x ∈ U i, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U i ∧
      ∀ᶠ k in atTop, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f k) V)

include hU he hc hlower hopen hconn happrox hflocal in
theorem exists_eventual_source_readout_neighborhood
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U i) :
    ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U i ∧
      ∀ᶠ k in atTop, ∀ y ∈ W,
        ContMDiffAt (𝓡 n) (𝓡 n) ∞ (f k) y ∧ f k y ∈ range (e k) := by
  let : LocallyCompactSpace (Piece U i) := (hU i).locallyCompactSpace
  obtain ⟨V, hV, hxV, hVU, hVsmooth⟩ := hflocal x hx
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hxV)
  have hKr : K ⊆ range (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) := by
    intro y hy
    exact ⟨⟨y, hVU (hKV hy)⟩, rfl⟩
  have hKi := (hU i).isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK hKr
  have hmem := eventually_mem_range_of_uniform_chart_approximation he hc hlower hopen
    hconn hKi (happrox _ hKi)
  refine ⟨interior K, isOpen_interior, hxK (mem_singleton x),
    interior_subset.trans (hKV.trans hVU), ?_⟩
  filter_upwards [hVsmooth, hmem] with k hks hkm y hy
  exact ⟨hks.contMDiffAt (hV.mem_nhds (hKV (interior_subset hy))),
    hkm ⟨y, hVU (hKV (interior_subset hy))⟩ (show y ∈ K from interior_subset hy)⟩

include he hc hlower hopen hconn happrox hflocal in
theorem source_pullbackCoefficients_tendsto_jets
    (hsmooth : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (g : ∀ k, RiemannianMetric n (M k))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (U i))
    (hBjet : ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (chartParametrization U hU (e k))))
      (iteratedFDeriv ℝ m B) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y => (Function.invFun (e k) (f k y)).val))
      (iteratedFDeriv ℝ m id) atTop K) :
    ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (f k)))
      (iteratedFDeriv ℝ m B) atTop K := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let a := fun k (y : EuclideanSpace ℝ (Fin n)) => (Function.invFun (e k) (f k y)).val
  have hlocal := fun x hx => exists_eventual_source_readout_neighborhood U hU
    he hc hlower hopen hconn happrox hflocal (x := x) hx
  have halocal : ∀ x ∈ U i, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := hlocal x hx
    refine ⟨W, hW, hxW, hs.mono fun k hk y hy => ?_⟩
    exact (contDiffAt_source_readout U hU (hsmooth k) (hopen k).injective
      (hopen k).isOpen_range (hk y hy).1 (hk y hy).2).contDiffWithinAt
  have hBlocal : ∀ x ∈ U i, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        ((g k).pullbackCoefficients (chartParametrization U hU (e k))) W := by
    intro x hx
    refine ⟨U i, hU i, hx, Eventually.of_forall fun k y hy => ?_⟩
    exact ((g k).contDiffAt_pullbackCoefficients
      ((contMDiffOn_chartParametrization U hU (hsmooth k).contMDiff).contMDiffAt
        ((hU i).mem_nhds hy))).contDiffWithinAt
  obtain ⟨_, hPjet⟩ := smooth_convergence_pullback_bilinear_on_open (hU i) (hU i)
    hB contDiff_id.contDiffOn (fun _ hx => hx) hBlocal halocal hBjet hajet
  have hPjet' : ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y =>
        ((g k).pullbackCoefficients (chartParametrization U hU (e k)) (a k y)).bilinearComp
          (fderiv ℝ (a k) y) (fderiv ℝ (a k) y))) (iteratedFDeriv ℝ m B) atTop K := by
    simpa only [id_eq, fderiv_id, ContinuousLinearMap.bilinearComp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.flip_flip] using hPjet
  intro m K hK hKU
  apply tendstoUniformlyOn_iteratedFDeriv_of_local_models (hU i) ?_ m hK hKU
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hs⟩ := hlocal x hx
  refine ⟨W, hW, hxW, hWU,
    (fun k y => ((g k).pullbackCoefficients (chartParametrization U hU (e k)) (a k y)).bilinearComp
      (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)), B, ?_, fun _ _ => rfl, ?_⟩
  · filter_upwards [hs] with k hk y hy
    exact (source_readout_pullbackCoefficients U hU (g k) (hsmooth k)
      (hopen k).injective (hopen k).isOpen_range (hk y hy).1 (hk y hy).2).symm
  · intro l C hC hCW
    exact hPjet' l C hC (hCW.trans hWU)

end PoincareConjecture.ChartDistance

import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.SpacetimePullback
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem contDiffOn_source_chart_spacetime_pullbackCoefficients
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {i : ι} {e : Piece U i → M}
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiff (𝓡 n) (𝓡 n) ∞ e)
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : IsOpen J) :
    ContDiffOn ℝ ∞
      (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g y.1).pullbackCoefficients (chartParametrization U hU e) y.2) (J ×ˢ U i) := by
  intro z hz
  exact (hg.contDiffAt_spacetime_pullbackCoefficients hJ
    ((contMDiffOn_chartParametrization U hU he).contMDiffAt ((hU i).mem_nhds hz.2))
    hz.1).contDiffWithinAt

theorem source_spacetime_pullbackCoefficients_tendsto_jets
    {ι : Type*} {n : ℕ}
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
    (hsmooth : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (J : Set ℝ) (hJ : IsOpen J)
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U i))
    (hBlocal : ∀ z ∈ J ×ˢ U i, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) y.2) W)
    (hBjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) y.2))
      (iteratedFDeriv ℝ m B) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y => (Function.invFun (e k) (f k y)).val))
      (iteratedFDeriv ℝ m id) atTop K) :
    ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y => (g k y.1).pullbackCoefficients (f k) y.2))
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
  obtain ⟨_, hPjet⟩ := smooth_convergence_spacetime_bilinear_pullback hJ (hU i)
    hB halocal hBlocal hajet hBjet
  intro m K hK hKU
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact (hJ.prod (hU i))).mp ?_ K hKU hK
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨W, hW, hzW, hWU, hs⟩ := hlocal z.2 hz.2
  have hzJW : z ∈ J ×ˢ W := ⟨hz.1, hzW⟩
  obtain ⟨C, ⟨hCn, hC⟩, hCJW⟩ :=
    (compact_basis_nhds z).mem_iff.mp ((hJ.prod hW).mem_nhds hzJW)
  have hCJU : C ⊆ J ×ˢ U i := fun y hy => ⟨(hCJW hy).1, hWU (hCJW hy).2⟩
  refine ⟨C, nhdsWithin_le_nhds hCn, (hPjet m C hC hCJU).congr ?_⟩
  filter_upwards [hs] with k hk
  have heq : EqOn
      (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) (a k y.2)).bilinearComp
          (fderiv ℝ (a k) y.2) (fderiv ℝ (a k) y.2))
      (fun y => (g k y.1).pullbackCoefficients (f k) y.2) (J ×ˢ W) := by
    intro y hy
    exact source_readout_pullbackCoefficients U hU (g k y.1) (hsmooth k)
      (hopen k).injective (hopen k).isOpen_range (hk y.2 hy.2).1 (hk y.2 hy.2).2
  exact (eqOn_iteratedFDeriv_of_isOpen (hJ.prod hW) heq m).mono hCJW

theorem source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (F : ∀ k, Quotient O.setoid → M k)
    (hF : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) (E k))
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
      (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop C)
    (hreadout : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (coordinateRepresentative U hU
          (fun x => Function.invFun (e k i) (F k (O.include i x)))))
      (iteratedFDeriv ℝ m id) atTop K)
    (J : Set ℝ) (hJ : IsOpen J)
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i))
    (hBlocal : ∀ i z, z ∈ J ×ˢ U i → ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k i)) y.2) W)
    (hBjet : ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K) :
    ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => (g k y.1).pullbackCoefficients
          (chartParametrization U hU (F k ∘ O.include i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K := by
  intro i
  apply source_spacetime_pullbackCoefficients_tendsto_jets U hU
    (fun k => he k i) (hc i) (fun k => hlower k i) (fun k => hopen k i)
    hconn ?_ ?_ (fun k => hsmooth k i) J hJ g (B i) (hB i) (hBlocal i) (hBjet i) ?_
  · intro C hC
    simpa only [chartParametrization_apply, Function.comp_apply] using happrox i C hC
  · intro x hx
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between isCompact_singleton (hU i)
      (singleton_subset_iff.mpr hx)
    refine ⟨interior K, isOpen_interior, hxK (mem_singleton x),
      interior_subset.trans hKU, ?_⟩
    exact (eventually_contMDiffOn_source_exhaustion_chart U hU O hO hE hEmono
      hEcover F hF i hK hKU).mono fun _ hk => hk.mono interior_subset
  · exact hreadout i

theorem source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets_of_smooth_families
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (F : ∀ k, Quotient O.setoid → M k)
    (hF : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) (E k))
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
      (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop C)
    (hreadout : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (coordinateRepresentative U hU
          (fun x => Function.invFun (e k i) (F k (O.include i x)))))
      (iteratedFDeriv ℝ m id) atTop K)
    (J : Set ℝ) (hJ : IsOpen J)
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn (g k) J)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i))
    (hBjet : ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K) :
    ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun y => (g k y.1).pullbackCoefficients
          (chartParametrization U hU (F k ∘ O.include i)) y.2))
      (iteratedFDeriv ℝ m (B i)) atTop K := by
  apply source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets U hU O hO
    hE hEmono hEcover F hF L he c hc hlower hopen hconn hsmooth happrox hreadout
    J hJ g B hB ?_ hBjet
  intro i z hz
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact ⟨J ×ˢ U i, hJ.prod (hU i), hz, Eventually.of_forall fun k =>
    contDiffOn_source_chart_spacetime_pullbackCoefficients U hU
      (hsmooth k i).contMDiff (hg k) hJ⟩

end PoincareConjecture.ChartDistance

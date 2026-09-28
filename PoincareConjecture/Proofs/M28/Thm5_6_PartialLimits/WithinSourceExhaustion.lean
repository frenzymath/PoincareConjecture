import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinSourceReadout











set_option autoImplicit false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance




theorem source_exhaustion_spacetime_pullbackCoefficients_tendsto_withinJets
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
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hconvJ : Convex ℝ J)
    [LocallyCompactSpace J]
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn (g k) J)
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i))
    (hBjet : ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k i)) y.2)
        (J ×ˢ U i))
      (iteratedFDerivWithin ℝ m (B i) (J ×ˢ U i)) atTop K) :
    ∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun y => (g k y.1).pullbackCoefficients
          (chartParametrization U hU (F k ∘ O.include i)) y.2) (J ×ˢ U i))
      (iteratedFDerivWithin ℝ m (B i) (J ×ˢ U i)) atTop K := by
  intro i
  apply source_spacetime_pullbackCoefficients_tendsto_withinJets U hU
    (fun k => he k i) (hc i) (fun k => hlower k i) (fun k => hopen k i)
    hconn ?_ ?_ (fun k => hsmooth k i) hJ hconvJ g hg (B i) (hB i) (hBjet i) ?_
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

end PoincareConjecture.ChartDistance

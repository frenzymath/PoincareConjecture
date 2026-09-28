import PoincareConjecture.Proofs.M28.Mathlib.WithinSpacetimePullback
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion

set_option autoImplicit false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem source_spacetime_pullbackCoefficients_tendsto_withinJets
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
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hconvJ : Convex ℝ J)
    [LocallyCompactSpace J]
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn (g k) J)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U i))
    (hBjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun y => (g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) y.2)
        (J ×ˢ U i))
      (iteratedFDerivWithin ℝ m B (J ×ˢ U i)) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y => (Function.invFun (e k) (f k y)).val))
      (iteratedFDeriv ℝ m id) atTop K) :
    ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun y => (g k y.1).pullbackCoefficients (f k) y.2) (J ×ˢ U i))
      (iteratedFDerivWithin ℝ m B (J ×ˢ U i)) atTop K := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let a := fun k (y : EuclideanSpace ℝ (Fin n)) => (Function.invFun (e k) (f k y)).val
  have hcoeff : ∀ k, ContDiffOn ℝ ∞
      (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) y.2)
      (J ×ˢ U i) := fun k =>
    (hg k).contDiffOn_spacetime_pullbackCoefficients_within (hU i)
      (contMDiffOn_chartParametrization U hU (hsmooth k).contMDiff)
  intro m K hK hKU
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨W, hW, hzW, hWU, hs⟩ := exists_eventual_source_readout_neighborhood U hU
    he hc hlower hopen hconn happrox hflocal (hKU hz).2
  obtain ⟨r, hr, hVr⟩ := Metric.isOpen_iff.mp hW z.2 hzW
  let V := ball z.2 r
  have hV : IsOpen V := isOpen_ball
  have hVU : V ⊆ U i := hVr.trans hWU
  have hzV : z.2 ∈ V := mem_ball_self hr
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : LocallyCompactSpace (J ×ˢ V) :=
    (Homeomorph.Set.prod J V).isOpenEmbedding.locallyCompactSpace
  have ha : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) V := by
    filter_upwards [hs] with k hk y hy
    exact (contDiffAt_source_readout U hU (hsmooth k) (hopen k).injective
      (hopen k).isOpen_range (hk y (hVr hy)).1 (hk y (hVr hy)).2).contDiffWithinAt
  have hmap : ∀ᶠ k in atTop, MapsTo (a k) V (U i) :=
    Eventually.of_forall fun k _ _ => (Function.invFun (e k) (f k _)).property
  obtain ⟨_, hPjet⟩ := tendstoUniformlyOn_withinJets_spacetime_bilinear_pullback
    hJ hconvJ (hU i) hV (convex_ball _ _) hVU ha hmap
    (Eventually.of_forall hcoeff) hB
    (fun l C hC hCV => hajet l C hC (hCV.trans hVU)) hBjet
  obtain ⟨C, ⟨hCn, hC⟩, hCV⟩ := (compact_basis_nhds z).mem_iff.mp
    ((hV.preimage continuous_snd).mem_nhds hzV)
  have hKCV : K ∩ C ⊆ J ×ˢ V := fun y hy => ⟨(hKU hy.1).1, hCV hy.2⟩
  refine ⟨K ∩ C, inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hCn), ?_⟩
  apply ((hPjet m (K ∩ C) (hK.inter_right hC.isClosed) hKCV).congr ?_).congr_right ?_
  · filter_upwards [hs] with k hk
    have heq : EqOn
        (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((g k y.1).pullbackCoefficients (chartParametrization U hU (e k)) (a k y.2)).bilinearComp
            (fderiv ℝ (a k) y.2) (fderiv ℝ (a k) y.2))
        (fun y => (g k y.1).pullbackCoefficients (f k) y.2) (J ×ˢ V) := by
      intro y hy
      exact source_readout_pullbackCoefficients U hU (g k y.1) (hsmooth k)
        (hopen k).injective (hopen k).isOpen_range
        (hk y.2 (hVr hy.2)).1 (hk y.2 (hVr hy.2)).2
    intro y hy
    exact (heq.iteratedFDerivWithin m (hKCV hy)).trans
      (iteratedFDerivWithin_prod_eq_of_isOpen _ m (hU i) hV
        (hKU hy.1).2 (hKCV hy).2).symm
  · intro y hy
    exact (iteratedFDerivWithin_prod_eq_of_isOpen B m (hU i) hV
      (hKU hy.1).2 (hKCV hy).2).symm

end PoincareConjecture.ChartDistance

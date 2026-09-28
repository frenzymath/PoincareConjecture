import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricFamilyLimit
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_smooth_metricFamilies_of_spacetime_bounds
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    {J : Set ℝ} (hJ : IsOpen J) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (g : ∀ k, ℝ → RiemannianMetric n (M k))
    (hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn (g k) J)
    (hjets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g k z.1).pullbackCoefficients (chartParametrization U hU (e k i)) z.2) p‖ ≤ C)
    (hpositive : ∀ t ∈ J, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        (g k t).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := overlapSystem hD L he c hc hlower hopen hconn
    let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ i j x y, Tendsto (fun k => dist (e (σ k) i x) (e (σ k) j y)) atTop
        (𝓝 (D i j (x, y)))) ∧
      ∃ B : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        (∀ i, ContDiffOn ℝ ∞ (B i) (J ×ˢ U i)) ∧
        (∀ i m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              (g (σ k) z.1).pullbackCoefficients
                (chartParametrization U hU (e (σ k) i)) z.2))
          (iteratedFDeriv ℝ m (B i)) atTop K) ∧
        ∃ (gLimit : ℝ → ∀ i, CanonicalMetric U hU i)
          (hcompat : ∀ t, CompatibleMetrics U hU O (gLimit t)),
          (∀ t ∈ J, ∀ i (x : Piece U i) v w,
            (gLimit t i).inner x v w = B i (t, x) v w) ∧
          (∀ i, RiemannianMetric.IsSmoothFamilyOn (fun t => gLimit t i) J) ∧
          RiemannianMetric.IsSmoothFamilyOn
            (fun t => quotientMetric U hU O hO (gLimit t) (hcompat t)) J := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let O := overlapSystem hD L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hsource (i k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g k z.1).pullbackCoefficients (chartParametrization U hU (e k i)) z.2)
      (J ×ˢ U i) := by
    intro p hp
    exact ((hg k).contDiffAt_spacetime_pullbackCoefficients hJ
      ((contMDiffOn_chartParametrization U hU (hsmooth k i).contMDiff).contMDiffAt
        ((hU i).mem_nhds hp.2)) hp.1).contDiffWithinAt
  obtain ⟨σ, hσ, B, hBsmooth, hBjets⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional
      (fun i => hJ.prod (hU i))
      (fun i k z => (g k z.1).pullbackCoefficients
        (chartParametrization U hU (e k i)) z.2) hsource hjets
  have hDσ : ∀ i j x y,
      Tendsto (fun k => dist (e (σ k) i x) (e (σ k) j y)) atTop
        (𝓝 (D i j (x, y))) := fun i j x y => (hD i j x y).comp hσ.tendsto_atTop
  have hBlocal (i : ℕ) : TendstoLocallyUniformlyOn
      (fun k z => (g (σ k) z.1).pullbackCoefficients
        (chartParametrization U hU (e (σ k) i)) z.2)
      (B i) atTop (J ×ˢ U i) :=
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hJ.prod (hU i)) (hBjets i 0)
  have hBslice : ∀ t ∈ J, ∀ i, TendstoLocallyUniformlyOn
      (fun k => (g (σ k) t).pullbackCoefficients (chartParametrization U hU (e (σ k) i)))
      (fun x => B i (t, x)) atTop (U i) := by
    intro t ht i
    have hmaps : MapsTo (fun x : EuclideanSpace ℝ (Fin n) => (t, x))
        (U i) (J ×ˢ U i) := fun _ hx => ⟨ht, hx⟩
    exact (hBlocal i).comp (fun x => (t, x)) hmaps
      (continuous_const.prodMk continuous_id).continuousOn
  have hpositiveσ : ∀ t ∈ J, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        (g (σ k) t).pullbackCoefficients (chartParametrization U hU (e (σ k) i)) x v v := by
    intro t ht i x hx
    obtain ⟨a, ha, hpos⟩ := hpositive t ht i x hx
    exact ⟨a, ha, hσ.tendsto_atTop.eventually hpos⟩
  have hboundσ : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e (σ k) j) (e (σ k) i x))) := by
    intro i j K hK hKU m
    obtain ⟨C, hC⟩ := hbound i j K hK hKU m
    exact ⟨C, hσ.tendsto_atTop.eventually hC⟩
  obtain ⟨gLimit, hcompat, hcoeff, hfamily, hquotient⟩ :=
    exists_compatibleMetricFamilies_of_spacetime_limits U hU hDσ L (fun k => he (σ k))
      c hc (fun k => hlower (σ k)) (fun k => hopen (σ k)) (fun k => hconn (σ k))
      (fun k => hsmooth (σ k)) t₀ ht₀ (fun k => g (σ k)) B hBslice hBsmooth
      hpositiveσ hboundσ
  exact ⟨σ, hσ, hDσ, B, hBsmooth, hBjets, gLimit, hcompat, hcoeff, hfamily, hquotient⟩

end PoincareConjecture.ChartDistance

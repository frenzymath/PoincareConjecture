import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionLimit

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
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in
theorem limit_coefficients_transition
    (g : ∀ k, RiemannianMetric n (M k))
    (B : ι → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, TendstoLocallyUniformlyOn
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
      (B i) atTop (U i))
    (hBcont : ∀ i, ContinuousOn (B i) (U i))
    (i j : ι)
    (hbound : LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    let f := coordinateRepresentative U hU (transition (fun i j => D i j) i j)
    ∀ x ∈ Subtype.val '' overlap (fun i j => D i j) i j, ∀ v w,
      B j (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = B i x v w := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  apply CoordinateTransition.pullback_eq_of_tendsto (hU j)
    (Aseq := fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
    (Bseq := fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k j)))
    (fseq := fun k => coordinateRepresentative U hU
      (fun x => Function.invFun (e k j) (e k i x)))
    ?_ (hB j) (hBcont j) ?_ ?_ ?_ ?_
  · intro x hx v w
    obtain ⟨x, hx, rfl⟩ := hx
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
        ((hB i).tendsto_at x.property))
  · rintro _ ⟨x, hx, rfl⟩
    rw [coordinateRepresentative_apply]
    exact (transition (fun i j => D i j) i j x).property
  · intro x hx
    exact coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn i j hx
  · intro x hx v
    have hjet := tendsto_coordinate_source_transition_jet U hU hD L he c hc hlower
      hopen hconn hsmooth i j hbound 1 hx
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin n)) (fun _ : Fin 1 => v)
    simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
      (hev.continuous.tendsto _).comp hjet
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, _, hxV, K, _, hrep⟩ :=
      exists_source_transition_neighborhood hD L he c hc hlower hopen hconn hx
    filter_upwards [hrep] with k hk v w
    exact source_transition_pullbackCoefficients U hU (g k) (hsmooth k i).contMDiff
      (hsmooth k j) (hopen k j).injective (hopen k j).isOpen_range x
      (image_subset_range _ _ (hk x hxV).1) v w

end PoincareConjecture.ChartDistance

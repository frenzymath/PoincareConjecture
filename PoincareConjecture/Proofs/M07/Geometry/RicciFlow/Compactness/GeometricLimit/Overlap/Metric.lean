import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricLimit
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.MetricLimit
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

theorem exists_canonicalMetric_of_coordinate_limit
    (Bseq : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (i : ι) (hsmooth : ContDiffOn ℝ ∞ B (U i))
    (hsymm : ∀ k x, x ∈ U i → ∀ v w, Bseq k x v w = Bseq k x w v)
    (hconv : ∀ x, x ∈ U i → ∀ v w,
      Tendsto (fun k => Bseq k x v w) atTop (𝓝 (B x v w)))
    (hlower : ∀ x, x ∈ U i → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ v, c * ‖v‖ ^ 2 ≤ Bseq k x v v) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ g : CanonicalMetric U hU i, ∀ (x : Piece U i) v w, g.inner x v w = B x v w := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  apply RiemannianMetric.exists_of_constant_chart_limit (M := Piece U i)
    (fun _ _ => rfl) (fun k x => Bseq k x) (fun x => B x) ?_
    (fun k x => hsymm k x x.property) (fun x => hconv x x.property)
    (fun x => hlower x x.property)
  intro x
  exact ((hsmooth x x.property).contDiffAt ((hU i).mem_nhds x.property)).contMDiffAt.comp x
    (contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞) (hU i).isOpenEmbedding_subtypeVal x)

variable {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
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
theorem exists_compatibleMetrics_of_coordinate_limits
    (g : ∀ k, RiemannianMetric n (M k))
    (B : ι → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, TendstoLocallyUniformlyOn
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
      (B i) atTop (U i))
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (U i))
    (hBlower : ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    ∃ gLimit : ∀ i, CanonicalMetric U hU i,
      (∀ i (x : Piece U i) v w, (gLimit i).inner x v w = B i x v w) ∧
      CompatibleMetrics U hU (overlapSystem hD L he c hc hlower hopen hconn) gLimit := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hex : ∀ i, ∃ gLimit : CanonicalMetric U hU i,
      ∀ (x : Piece U i) v w, gLimit.inner x v w = B i x v w := by
    intro i
    apply exists_canonicalMetric_of_coordinate_limit U hU
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
      (B i) i (hBsmooth i) ?_ ?_ (hBlower i)
    · intro k x hx v w
      exact (g k).symm _ _ _
    · intro x hx v w
      exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
        (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
          ((hB i).tendsto_at hx))
  choose gLimit hgLimit using hex
  refine ⟨gLimit, hgLimit, ?_⟩
  have hs := overlapSystem_smooth U hU hD L he c hc hlower hopen hconn hsmooth hbound
  intro i j x hx v w
  have hm := limit_coefficients_transition U hU hD L he c hc hlower hopen hconn hsmooth
    g B hB (fun i => (hBsmooth i).continuousOn) i j (hbound i j)
    x (mem_image_of_mem Subtype.val hx) v w
  have ht := (hs i j).contMDiffAt
    (((overlapSystem hD L he c hc hlower hopen hconn).transition i j).open_source.mem_nhds hx)
  have hd := mfderiv_eq_coordinateRepresentative U hU x (ht.mdifferentiableAt (by simp))
  simp only [hgLimit, hd]
  change B i x v w = B j (transition (fun i j => D i j) i j x)
    (fderiv ℝ (coordinateRepresentative U hU (transition (fun i j => D i j) i j)) x v)
    (fderiv ℝ (coordinateRepresentative U hU (transition (fun i j => D i j) i j)) x w)
  simpa only [coordinateRepresentative_apply] using hm.symm

end PoincareConjecture.ChartDistance

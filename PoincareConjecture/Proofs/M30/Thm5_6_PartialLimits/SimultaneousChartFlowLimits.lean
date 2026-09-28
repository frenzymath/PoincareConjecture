import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateFlowCurvature
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching.OperatorPositivity
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}

private theorem coordinateFlow_nonnegative_of_defect_tendsto
    {V : Set (EuclideanSpace ℝ (Fin 3))} {hV : IsOpen V} [Nonempty V]
    {e : ∀ k, V → M k} (L : M28.FixedCoordinateFlowLimit F V hV e)
    (htau : 0 < tau)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k))
    (hdefect : ∀ t ∈ Icc (-tau) 0, ∀ x : V,
      Tendsto (fun k => ((F (L.subsequence k)).connection t).negativeCurvaturePart
        (e (L.subsequence k) x)) atTop (𝓝 0)) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ x : V,
      (L.flow.connection t).NonnegativeCurvatureOperator x := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro t ht x
  apply (L.flow.connection t).nonnegativeCurvatureOperator_of_plane_nonneg
    (L.flow.connection t).normalization_curvatureTensorCalculus x
  intro v w
  let param (k : ℕ) := chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (i := ()) (e (L.subsequence k))
  let dv (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (param k) x v
  let dw (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (param k) x w
  have hz : Tendsto (fun k => ((F (L.subsequence k)).connection t).negativeCurvaturePart
      (param k x)) atTop (𝓝 0) := by
    simpa only [param, chartParametrization_apply] using hdefect t ht x
  have hgram : Tendsto
      (fun k => M04.metricGram ((F (L.subsequence k)).metric t) (param k x) (dv k) (dw k))
      atTop (𝓝 (M04.metricGram (L.flow.metric t) x v w)) := by
    simpa only [M04.metricGram, RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply, param, dv, dw] using!
      ((L.metric_inner_tendsto htau he t ht x v v).mul
        (L.metric_inner_tendsto htau he t ht x w w)).sub
          ((L.metric_inner_tendsto htau he t ht x v w).pow 2)
  have hlo : Tendsto
      (fun k => -((F (L.subsequence k)).connection t).negativeCurvaturePart (param k x) *
        M04.metricGram ((F (L.subsequence k)).metric t) (param k x) (dv k) (dw k))
      atTop (𝓝 (0 : ℝ)) := by simpa only [neg_zero, zero_mul] using hz.neg.mul hgram
  have hRm := L.curvatureTensor_tendsto htau he t ht x v w v w
  apply le_of_tendsto_of_tendsto hlo hRm
  exact Eventually.of_forall fun k =>
    ((F (L.subsequence k)).connection t).curvatureTensor_plane_ge_negativePart_mul_gram
      ((F (L.subsequence k)).connection t).normalization_curvatureTensorCalculus
        (param k x) (dv k) (dw k)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in

theorem exists_simultaneous_nonnegative_coordinateFlowLimits
    (htau : 0 < tau) (F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0))
    (V : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hV : ∀ i, IsOpen (V i))
    [∀ i, Nonempty (V i)] (hconv : ∀ i, Convex ℝ (V i))
    (e : ∀ i k, V i → M k)
    (he : ∀ i, letI := (hV i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i k))
    (hell : ∀ i, ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V i, ∀ v,
        alpha * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients
          (chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
            (i := ()) (e i k)) x v v)
    (hbound : ∀ i K, IsCompact K → K ⊆ Icc (-tau) 0 ×ˢ V i → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((F k).metric z.1).pullbackCoefficients
            (chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
              (i := ()) (e i k)) z.2) (Icc (-tau) 0 ×ˢ V i) z‖ ≤ B)
    (hdefect : ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-tau) 0, ∀ x : M k, ((F k).connection t).negativeCurvaturePart x ≤ eta) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ L : ∀ i, M28.FixedCoordinateFlowLimit F (V i) (hV i) (e i),
        (∀ i, (L i).subsequence = sigma) ∧
        ∀ i, letI := (hV i).isOpenEmbedding_subtypeVal.singletonChartedSpace
          letI := (hV i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
          ∀ t ∈ Icc (-tau) 0, ∀ x : V i,
            ((L i).flow.connection t).NonnegativeCurvatureOperator x := by
  classical
  let J := Icc (-tau) 0
  let f (i k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin 3)) :=
    ((F k).metric z.1).pullbackCoefficients
      (chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
        (i := ()) (e i k)) z.2
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by linarith)
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith, le_rfl⟩
  let : LocallyCompactSpace J := isClosed_Icc.locallyCompactSpace
  let : ∀ i, LocallyCompactSpace (V i) := fun i => (hV i).locallyCompactSpace
  let : ∀ i, LocallyCompactSpace (J ×ˢ V i) := fun i =>
    (Homeomorph.Set.prod J (V i)).isOpenEmbedding.locallyCompactSpace
  have hsmooth (i k : ℕ) : ContDiffOn ℝ ∞ (f i k) (J ×ˢ V i) := by
    let := (hV i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    exact (F k).smooth.contDiffOn_spacetime_pullbackCoefficients_within (hV i)
      (contMDiffOn_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
        (i := ()) (he i k).contMDiff)
  obtain ⟨sigma, hsigma, B, hB, hjets⟩ :=
    exists_common_contDiffOn_subsequence_of_withinJet_bounds
      (fun i => J ×ˢ V i) (fun i => (convex_Icc (-tau) 0).prod (hconv i))
      (fun i => hJ.prod (hV i).uniqueDiffOn) f hsmooth hbound
  have hex (i : ℕ) : ∃ L : M28.FixedCoordinateFlowLimit F (V i) (hV i) (e i),
      L.subsequence = sigma := by
    let := (hV i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    let := (hV i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    let U : Unit → Set (EuclideanSpace ℝ (Fin 3)) := fun _ => V i
    let hU : ∀ a, IsOpen (U a) := fun _ => hV i
    obtain ⟨alpha, halpha, helli⟩ := hell i
    have hpoint (t : ℝ) (ht : t ∈ J) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ V i) :
        Tendsto (fun k => f i (sigma k) (t, x)) atTop (𝓝 (B i (t, x))) := by
      have hjet := hjets i 0 {(t, x)} isCompact_singleton
        (singleton_subset_iff.mpr ⟨ht, hx⟩)
      have hcoeff := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn hjet
      simpa only [Function.comp_apply, iteratedFDerivWithin_zero_apply] using
        hcoeff.tendsto_at (mem_singleton (t, x))
    have hmetric : ∀ t : J, ∃ g : CanonicalMetric U hU (),
        ∀ (x : V i) v w, g.inner x v w = B i (t, x) v w := by
      intro t
      apply exists_canonicalMetric_of_coordinate_limit U hU
        (fun k => ((F (sigma k)).metric t).pullbackCoefficients
          (chartParametrization U hU (i := ()) (e i (sigma k)))) (fun x => B i (t, x)) ()
      · exact (hB i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun x hx => ⟨t.property, hx⟩)
      · intro k x _ v w
        exact ((F (sigma k)).metric t).symm _ _ _
      · intro x hx v w
        exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
          (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
            (hpoint t t.property x hx))
      · intro x hx
        exact ⟨alpha, halpha, (hsigma.tendsto_atTop.eventually helli).mono
          fun k hk v => hk t t.property x hx v⟩
    choose gSlice hgSlice using hmetric
    let g : ℝ → CanonicalMetric U hU () := fun t =>
      if ht : t ∈ J then gSlice ⟨t, ht⟩ else gSlice ⟨0, hzero⟩
    have hcoeff : ∀ t ∈ J, ∀ (x : V i) v w, (g t).inner x v w = B i (t, x) v w := by
      intro t ht x v w
      simpa only [g, dif_pos ht] using hgSlice ⟨t, ht⟩ x v w
    have hg : RiemannianMetric.IsSmoothFamilyOn g J :=
      canonicalMetric_isSmoothFamilyOn_of_coefficients U hU () g (B i) (hB i) hcoeff
    obtain ⟨F0, hF0⟩ := exists_ricciFlow_on_within_coordinate_limit U hU hJ
      (fun k => F (sigma k)) () (fun k => e i (sigma k)) (fun k => he i (sigma k))
      g hg (B i) hcoeff (hjets i)
    refine ⟨{
      subsequence := sigma
      subsequence_strictMono := hsigma
      coefficients := B i
      coefficients_smooth := hB i
      jets := hjets i
      flow := F0
      metric_coefficients := ?_ }, rfl⟩
    simpa only [hF0] using hcoeff
  choose L hL using hex
  refine ⟨sigma, hsigma, L, hL, ?_⟩
  intro i
  apply coordinateFlow_nonnegative_of_defect_tendsto (L i) htau (he i)
  intro t ht x
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [(L i).subsequence_strictMono.tendsto_atTop.eventually
    (hdefect (eta / 2) (by positivity))] with k hk
  have hnonneg : 0 ≤ ((F ((L i).subsequence k)).connection t).negativeCurvaturePart
      (e i ((L i).subsequence k) x) := le_max_right _ _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    (hk t ht (e i ((L i).subsequence k) x)).trans_lt (half_lt_self heta)

end PoincareConjecture.M30

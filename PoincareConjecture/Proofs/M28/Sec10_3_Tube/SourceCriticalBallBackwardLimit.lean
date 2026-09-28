import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardRestriction
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinLocalFlows
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CoordinateFamily

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2000000 in

structure BackwardChartLimit (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a) where

  subsequence : ℕ → ℕ

  subsequence_strictMono : StrictMono subsequence

  coefficients : ℝ × EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ

  coefficients_smooth : ContDiffOn ℝ ∞ coefficients
    (Icc (-(a / 8)) 0 ×ˢ D.limitDomain)

  jets : ∀ m L, IsCompact L → L ⊆ Icc (-(a / 8)) 0 ×ˢ D.limitDomain →
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z => ((D.sourceFlow (subsequence k)).metric z.1).pullbackCoefficients
          (D.limitParametrization (subsequence k)) z.2) (Icc (-(a / 8)) 0 ×ˢ D.limitDomain))
      (iteratedFDerivWithin ℝ m coefficients (Icc (-(a / 8)) 0 ×ˢ D.limitDomain)) atTop L

  flow : letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    RicciFlow 3 D.limitDomain (Icc (-(a / 8)) 0)

  metric_coefficients :
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-(a / 8)) 0, ∀ (x : D.limitDomain) v w,
      (flow.metric t).inner x v w = coefficients (t, x) v w

  terminal_coefficients :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (x : D.limitDomain) v w, (flow.metric 0).inner x v w =
      G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) q).symm x v w

variable (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in

theorem exists_backward_limit {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K)
    (hderiv : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ k t, t ∈ Icc (-(a / 8)) 0 →
      ∀ x ∈ D.domain, ((D.sourceFlow k).connection t).curvatureDerivativeNorm m
        (D.parametrization k x) ≤ B) : Nonempty (BackwardChartLimit D) := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let U : Unit → Set (EuclideanSpace ℝ (Fin 3)) := fun _ => D.limitDomain
  let hU : ∀ i, IsOpen (U i) := fun _ => D.limitDomain_open
  let J := Icc (-(a / 8)) 0
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by linarith [D.scale_pos])
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith [D.scale_pos], le_rfl⟩
  obtain ⟨eta, heta, B, hB, hjets, hterminal⟩ := D.exists_backward_coefficient_limit hK hcurv hderiv
  have hjets' : ∀ m L, IsCompact L → L ⊆ J ×ˢ D.limitDomain → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z => ((D.sourceFlow (eta k)).metric z.1).pullbackCoefficients
          (D.limitParametrization (eta k)) z.2) (J ×ˢ D.limitDomain))
      (iteratedFDerivWithin ℝ m B (J ×ˢ D.limitDomain)) atTop L := by
    intro m L hL hsub
    apply (hjets m L hL hsub).congr
    apply Eventually.of_forall
    intro k
    have heq : EqOn
        (fun z => ((D.sourceFlow (eta k)).metric z.1).pullbackCoefficients
          (D.parametrization (eta k)) z.2)
        (fun z => ((D.sourceFlow (eta k)).metric z.1).pullbackCoefficients
          (D.limitParametrization (eta k)) z.2) (J ×ˢ D.limitDomain) :=
      fun z hz => (D.limitParametrization_coefficients_eq (eta k) z.1 hz.2).symm
    exact (heq.iteratedFDerivWithin m).mono hsub
  have hpoint (t : ℝ) (ht : t ∈ J) (x : EuclideanSpace ℝ (Fin 3))
      (hx : x ∈ D.limitDomain) :
      Tendsto (fun k => ((D.sourceFlow (eta k)).metric t).pullbackCoefficients
        (D.limitParametrization (eta k)) x) atTop (𝓝 (B (t, x))) := by
    have hjet := hjets' 0 {(t, x)} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hx⟩)
    have hcoeff := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_apply, iteratedFDerivWithin_zero_apply] using
      hcoeff.tendsto_at (mem_singleton (t, x))
  obtain ⟨alpha, _, halpha, _, hell⟩ := D.evolving_ellipticity hK hcurv
  have hex : ∀ t : J, ∃ g : CanonicalMetric U hU (),
      ∀ (x : D.limitDomain) v w, g.inner x v w = B (t, x) v w := by
    intro t
    apply exists_canonicalMetric_of_coordinate_limit U hU
      (fun k => ((D.sourceFlow (eta k)).metric t).pullbackCoefficients
        (D.limitParametrization (eta k))) (fun x => B (t, x)) ()
    · exact hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x hx => ⟨t.property, hx⟩)
    · intro k x _ v w
      exact ((D.sourceFlow (eta k)).metric t).symm _ _ _
    · intro x hx v w
      exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
        (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
          (hpoint t t.property x hx))
    · intro x hx
      refine ⟨alpha, halpha, ?_⟩
      filter_upwards [heta.tendsto_atTop.eventually hell] with k hk
      intro v
      rw [D.limitParametrization_coefficients_eq (eta k) t hx]
      exact (hk t t.property x (D.limitDomain_subset_testSet hx) v).1
  choose gSlice hgSlice using hex
  let g : ℝ → CanonicalMetric U hU () := fun t =>
    if ht : t ∈ J then gSlice ⟨t, ht⟩ else gSlice ⟨0, hzero⟩
  have hcoeff : ∀ t ∈ J, ∀ (x : D.limitDomain) v w, (g t).inner x v w = B (t, x) v w := by
    intro t ht x v w
    simpa only [g, dif_pos ht] using hgSlice ⟨t, ht⟩ x v w
  have hg : RiemannianMetric.IsSmoothFamilyOn g J :=
    canonicalMetric_isSmoothFamilyOn_of_coefficients U hU () g B hB hcoeff
  obtain ⟨F, hF⟩ := exists_ricciFlow_on_within_coordinate_limit U hU hJ
    (fun k => D.sourceFlow (eta k)) () (fun k => D.limitNeckMap (eta k))
    (fun k => D.limitNeckMap_localDiffeomorph (eta k)) g hg B hcoeff hjets'
  refine ⟨{
    subsequence := eta
    subsequence_strictMono := heta
    coefficients := B
    coefficients_smooth := hB
    jets := hjets'
    flow := F
    metric_coefficients := ?_
    terminal_coefficients := ?_ }⟩
  · simpa only [hF] using hcoeff
  · intro x v w
    rw [hF, hcoeff 0 hzero, hterminal x x.property]

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

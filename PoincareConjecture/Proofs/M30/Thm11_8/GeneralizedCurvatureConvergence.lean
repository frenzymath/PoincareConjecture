import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedBilinearSpatialJets
import PoincareConjecture.Proofs.M30.Thm11_8.UniformCurvatureJets
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.SpatialContinuity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M28.Mathlib.FiniteChartCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

open SpacetimeBounds

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem eventually_generalized_chart_curvature_error
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ blowupMetricChartDomain G.limit q)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ k in atTop,
      K ⊆ Icc (-G.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ p ∈ K, (extChartAt (𝓡 3) q).symm p.2 ∈ G.exhaustion.space k ∧
        ∀ ht : p.1 ∈ Icc (-G.exhaustion.time k) 0,
          |(S.flow (G.subsequence k)).curvatureNorm
              ((G.embedding k).pointMap p.1 ht ((extChartAt (𝓡 3) q).symm p.2)) /
                S.scale (G.subsequence k) -
            (G.limit.flow.connection p.1).curvatureTensorNorm
              ((extChartAt (𝓡 3) q).symm p.2)| < delta := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let g := fun t => (G.limit.flow.metric t).pullbackCoefficients c.symm
  let A := fun k (p : ℝ × E) => metricTwoJet
    (fun x => generalizedPullbackCoefficients G k q (p.1, x)) p.2
  let A0 := fun p : ℝ × E => metricTwoJet (g p.1) p.2
  have hjets : TendstoUniformlyOn A A0 atTop K :=
    tendstoUniformlyOn_metricTwoJet_of_uniform_spatial_jets
      (f := fun k t x => generalizedPullbackCoefficients G k q (t, x))
      (g := g) (K := K) (l := atTop) (n := 3)
      (fun m _ => tendstoUniformlyOn_generalized_bilinear_spatial_jets G q m hK hKc)
  let Jtime : SpacetimeInterval := ⟨J, G.limit.flow.interval, G.limit.flow.nontrivial⟩
  have hcoeff := G.limit.flow.smooth.contDiffOn_spacetime_pullbackCoefficients_within
    (isOpen_extChartAt_target (I := 𝓡 3) q) (contMDiffOn_extChartAt_symm q)
  have hfinite : ContinuousOn (Bootstrap.spatialJet 2 (fun p : ℝ × E => g p.1 p.2))
      (J ×ˢ c.target) := by
    apply continuousOn_pi.mpr
    intro m
    exact M28.continuousOn_spatialJet_of_within
      (Proofs.M11.interval_uniqueDiffOn Jtime)
      (isOpen_extChartAt_target (I := 𝓡 3) q) hcoeff m
  have hA0 : ContinuousOn A0 K := by
    have H := ((twoJetProjection 3).continuous.comp_continuousOn hfinite).mono hKc
    apply H.congr
    intro p _hp
    exact (twoJetProjection_spatialJet (fun z : ℝ × E => g z.1 z.2) p).symm
  have hinvertible : ∀ p ∈ K, (A0 p).1.IsInvertible := fun p hp =>
    (G.limit.flow.metric p.1).isInvertible_chartCoefficients q (hKc hp).2
  have hcurvature := tendstoUniformlyOn_jetCurvatureNorm_of_uniform_jets
    hK hA0 hinvertible hjets
  have hc : ContinuousOn c.symm c.target := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn
  have hmap : ContinuousOn (fun p : ℝ × E => c.symm p.2) K :=
    hc.comp continuousOn_snd (fun p hp => (hKc hp).2)
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G (hK.image_of_continuousOn hmap)
  have htime := G.exhaustion.time_cofinal (Prod.fst '' K)
    (hK.image continuous_fst) (by rintro _ ⟨p, hp, rfl⟩; exact (hKc hp).1)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hcurvature delta hdelta,
    htime, eventually_ge_atTop j] with k hk htk hjk
  refine ⟨fun p hp => ⟨htk (mem_image_of_mem _ hp), (hKc hp).2⟩, ?_⟩
  intro p hp
  have hstage : c.symm p.2 ∈ G.exhaustion.space k :=
    G.exhaustion.space_increasing hjk (hj (mem_image_of_mem _ hp))
  refine ⟨hstage, ?_⟩
  intro ht
  let e := generalizedSliceHomeomorph G k p.1 ht
  let h := normalizedBlowupSliceMetric S (G.subsequence k) p.1
  let D := M13.scaleLeviCivitaData
    ((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + p.1 / S.scale (G.subsequence k)))
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))
  let V := c.target ∩ c.symm ⁻¹' G.exhaustion.space k
  have hV : IsOpen V := hc.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓡 3) q) (G.exhaustion.space_open k)
  have hchart (y : E) (hy : y ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hy)
  have hdiff : e.MDifferentiable (𝓡 3) (𝓡 3) := by
    constructor
    · intro x hx
      exact ((generalizedSliceHomeomorph_contMDiffAt G k p.1 ht hx).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
    · intro y hy
      exact ((generalizedSliceHomeomorph_symm_contMDiffAt G k p.1 ht hy).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ c.symm) V := by
    intro y hy
    exact ((generalizedSliceHomeomorph_contMDiffAt G k p.1 ht hy.2).comp y
      (hchart y hy.1)).contMDiffWithinAt
  have hi : ∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3) (e ∘ c.symm) y).IsInvertible := by
    intro y hy
    rw [mfderiv_comp y (hdiff.mdifferentiableAt hy.2)
      ((hchart y hy.1).mdifferentiableAt (by simp))]
    exact (show (mfderiv (𝓡 3) (𝓡 3) e (c.symm y)).IsInvertible from
      ⟨hdiff.mfderiv hy.2, rfl⟩).comp
        (Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy.1)
  have hpull := M28.jetCurvatureNorm_metricTwoJet_pullback D hV he hi
    (show p.2 ∈ V from ⟨(hKc hp).2, hstage⟩)
  have hhom := M13.identity_metricHomothety
    ((S.flow (G.subsequence k)).metric
      ((S.base (G.subsequence k)).1 + p.1 / S.scale (G.subsequence k)))
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))
  have hscale := M13.homothety_curvatureTensorNorm_eq _ h
    (Diffeomorph.refl (𝓡 3) _ ∞) (S.scale (G.subsequence k))
    (S.base_scalar_pos (G.subsequence k)) hhom
    ((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + p.1 / S.scale (G.subsequence k))) D (e (c.symm p.2))
  have hsource : M28.jetCurvatureNorm (A k p) =
      (S.flow (G.subsequence k)).curvatureNorm
        ((G.embedding k).pointMap p.1 ht (c.symm p.2)) / S.scale (G.subsequence k) := by
    have hactual : (fun y => generalizedPullbackCoefficients G k q (p.1, y)) =
        h.pullbackCoefficients (e ∘ c.symm) := by
      funext y
      simp only [generalizedPullbackCoefficients, dif_pos ht]
      rfl
    dsimp only [A]
    rw [hactual]
    exact hpull.trans hscale
  have htarget : M28.jetCurvatureNorm (A0 p) =
      (G.limit.flow.connection p.1).curvatureTensorNorm (c.symm p.2) :=
    M28.jetCurvatureNorm_metricTwoJet_pullback (G.limit.flow.connection p.1)
      (isOpen_extChartAt_target (I := 𝓡 3) q) (contMDiffOn_extChartAt_symm q)
      (fun y hy => Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy)
      (hKc hp).2
  have H := hk p hp
  rw [hsource, htarget] at H
  simpa only [Real.dist_eq, abs_sub_comm] using H

theorem eventually_generalized_curvature_error
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    {I : Set ℝ} (hI : IsCompact I) (hIJ : I ⊆ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ k in atTop,
      I ⊆ Icc (-G.exhaustion.time k) 0 ∧ K ⊆ G.exhaustion.space k ∧
      ∀ t ∈ I, ∀ ht : t ∈ Icc (-G.exhaustion.time k) 0, ∀ x ∈ K,
        |(S.flow (G.subsequence k)).curvatureNorm
            ((G.embedding k).pointMap t ht x) / S.scale (G.subsequence k) -
          (G.limit.flow.connection t).curvatureTensorNorm x| < delta := by
  classical
  let : LocallyCompactSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier
  obtain ⟨s, C, hC, hcover⟩ :=
    hK.exists_finite_extChart_cover (𝓡 3) isOpen_univ (subset_univ _)
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr fun q hq =>
    eventually_generalized_chart_curvature_error G q (hI.prod (hC q hq).2.2.2.2.1)
      (Set.prod_mono hIJ (hC q hq).2.2.2.2.2) hdelta
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G hK
  filter_upwards [hall, G.exhaustion.time_cofinal I hI hIJ, eventually_ge_atTop j]
    with k hk htime hjk
  refine ⟨htime, fun x hx => G.exhaustion.space_increasing hjk (hj hx), ?_⟩
  intro t htI ht x hx
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
  have hxC : x ∈ C q := interior_subset hxq
  have hxsource := ((hC q hq).2.2.2.1 hxC).1
  have H := ((hk q hq).2 (t, (extChartAt (𝓡 3) q) x)
    ⟨htI, mem_image_of_mem _ hxC⟩).2 ht
  simpa only [(extChartAt (𝓡 3) q).left_inv hxsource] using H

end PoincareConjecture.M30

import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCoefficientRegularity
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedSpatialSlices
import PoincareConjecture.Proofs.M30.Mathlib.VaryingSpatialJets
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient
import PoincareConjecture.Proofs.M11.IntervalTopology











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold





theorem tendstoUniformlyOn_generalized_scalar_spatial_jets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    (r : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ blowupMetricChartDomain G.limit q) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ r
        (fun y => blowupPullbackCoefficient (G.embedding k) q a b (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ r
        (fun y => (G.limit.flow.metric p.1).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p.2)
      atTop K := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let f := fun k => blowupPullbackCoefficient (G.embedding k) q a b
  let g := FlowCarrier.coordinateCoefficient G.limit.carrier q
    (fun t x v w => (G.limit.flow.metric t).inner x v w) a b
  let W := fun k => Icc (-G.exhaustion.time k) 0
  have hc : ContinuousOn c.symm c.target := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn
  have hmap : ContinuousOn (fun p : ℝ × E => c.symm p.2) K :=
    hc.comp continuousOn_snd (fun p hp => (hKc hp).2)
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G (hK.image_of_continuousOn hmap)
  let V := c.target ∩ c.symm ⁻¹' G.exhaustion.space j
  have hV : IsOpen V := hc.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓡 3) q) (G.exhaustion.space_open j)
  have hKV : K ⊆ J ×ˢ V := fun p hp =>
    ⟨(hKc hp).1, (hKc hp).2, hj (mem_image_of_mem _ hp)⟩
  have htest : K ⊆ {p | p ∈ blowupMetricChartDomain G.limit q ∧
      c.symm p.2 ∈ G.exhaustion.space j} := fun p hp =>
    ⟨hKc hp, hj (mem_image_of_mem _ hp)⟩
  have hfull : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ r (f k) (W k ×ˢ c.target))
      (iteratedFDerivWithin ℝ r g (J ×ˢ c.target)) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro delta hdelta
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r K hK htest delta hdelta
    filter_upwards [eventually_ge_atTop N] with k hk p hp
    simpa only [f, g, W, c, blowupMetricChartDomain, dist_eq_norm, norm_sub_rev]
      using (hN k hk).2 a b p hp
  have hjet : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ r (f k) (W k ×ˢ V))
      (iteratedFDerivWithin ℝ r g (J ×ˢ V)) atTop K := by
    apply (hfull.congr ?_).congr_right ?_
    · exact Filter.Eventually.of_forall fun k p hp =>
        iteratedFDerivWithin_prod_eq_of_isOpen (f k) r
          (isOpen_extChartAt_target (I := 𝓡 3) q) hV (hKc hp).2 (hKV hp).2
    · intro p hp
      exact iteratedFDerivWithin_prod_eq_of_isOpen g r
        (isOpen_extChartAt_target (I := 𝓡 3) q) hV (hKc hp).2 (hKV hp).2
  have hKsource : ∀ᶠ k in atTop, K ⊆ W k ×ˢ V := by
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r K hK htest 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with k hk p hp
    exact ⟨((hN k hk).1 hp).1, (hKV hp).2⟩
  have hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) (W k ×ˢ V) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    apply contDiffOn_generalized_pullback_coefficient G k q hV inter_subset_left
    rintro _ ⟨x, hx, rfl⟩
    exact G.exhaustion.space_increasing hk hx.2
  have hcoeff := G.limit.flow.smooth.contDiffOn_spacetime_pullbackCoefficients_within
    hV ((contMDiffOn_extChartAt_symm q).mono inter_subset_left)
  have hg : ContDiffOn ℝ ∞ g (J ×ˢ V) :=
    (hcoeff.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  let Jtime : SpacetimeInterval := ⟨J, G.limit.flow.interval, G.limit.flow.nontrivial⟩
  exact hjet.iteratedFDeriv_spatial_slice_varying_domain
    (Proofs.M11.interval_uniqueDiffOn Jtime) hV hKV
    (Filter.Eventually.of_forall fun k => uniqueDiffOn_Icc
      (neg_lt_zero.mpr (G.exhaustion.time_pos k))) hKsource hf hg
      (by exact_mod_cast le_top)

end PoincareConjecture.M30

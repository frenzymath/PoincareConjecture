import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetricJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_GeodesicTransport
import PoincareConjecture.Proofs.M44.Mathlib.SmoothLocalFactorization
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance terminalPullbackNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalPullbackSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance terminalPullbackTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance terminalPullbackTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem compactSmooth_preterminal_in_chart
    (event : SurgeryEventData g0 K P slice metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ event.regular_limit)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hregular : (extChartAt (𝓡 3) q).symm '' U ⊆ event.regular_limit)
    {tseq : ℕ → ℝ} (htseq : Tendsto tseq atTop (𝓝[<] T)) :
    CompactSmoothConvergenceOn
      (fun n => (event.pre_flow.metric (tseq n)).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm)
      (event.limit_metric.pullbackCoefficients
        (event.limit_identify.map ∘ (extChartAt (𝓡 3) q).symm)) atTop U := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).mono hchart
  have hf := event.limit_identify.map_smooth.comp hc
    (fun x hx => hregular (mem_image_of_mem _ hx))
  refine ⟨hU, ?_, ?_, ?_⟩
  · intro x hx
    exact (event.limit_metric.contDiffAt_pullbackCoefficients
      (hf.contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  · intro L _ hLU
    exact Eventually.of_forall fun n x hx =>
      (event.pre_flow.metric (tseq n)).contDiffAt_pullbackCoefficients
        (hc.contMDiffAt (hU.mem_nhds (hLU hx)))
  · intro j L hL hLU
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eta heta
    obtain ⟨d, hd, hbound⟩ := bilinear_jets_of_surgeryMetricLimitOn event.metric_converges
      q hq hU hchart hregular hf j hL hLU heta
    filter_upwards [htseq.eventually (Ioo_mem_nhdsLT (by linarith : T - d < T))]
      with n hn x hx
    simpa only [dist_eq_norm, norm_sub_rev] using hbound (tseq n) hn.1 hn.2 x hx

theorem tendsto_preterminal_pullback_jet
    (event : SurgeryEventData g0 K P slice metric T)
    {A : E → (slice event.tMinus).carrier} {V : Set E} (hV : IsOpen V)
    (hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V)
    (hregular : MapsTo A V event.regular_limit) {x : E} (hx : x ∈ V) (j : ℕ) :
    Tendsto (fun t => iteratedFDeriv ℝ j ((event.pre_flow.metric t).pullbackCoefficients A) x)
      (𝓝[<] T) (𝓝 (iteratedFDeriv ℝ j (event.limit_metric.pullbackCoefficients
        (event.limit_identify.map ∘ A)) x)) := by
  obtain ⟨U, W, hU, hW, hxW, _, hchart, hinside, k, hk, hmap, hfactor⟩ :=
    Poincare.exists_smooth_local_chart_factorization hV event.regular_limit_open hA hregular hx
  let q := A x
  let c := extChartAt (𝓡 3) q
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm U :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).mono hchart
  have hf := event.limit_identify.map_smooth.comp hc
    (fun y hy => hinside (mem_image_of_mem _ hy))
  apply Filter.tendsto_of_seq_tendsto
  intro tseq htseq
  have hbase := compactSmooth_preterminal_in_chart event q (hregular hx)
    hU hchart hinside htseq
  have hpull := hbase.pullback_bilinear
    (CompactSmoothConvergenceOn.constant (ι := ℕ) (l := atTop) hW hk) hmap
  have hactual : CompactSmoothConvergenceOn
      (fun n => (event.pre_flow.metric (tseq n)).pullbackCoefficients A)
      (event.limit_metric.pullbackCoefficients (event.limit_identify.map ∘ A)) atTop W := by
    apply hpull.congr
    · intro n y hy
      have hgerm : c.symm ∘ k =ᶠ[𝓝 y] A :=
        eventually_of_mem (hW.mem_nhds hy) (fun z hz => (hfactor z hz).symm)
      ext v w
      exact (event.pre_flow.metric (tseq n)).pullbackCoefficients_eq_of_comp_germ
        ((hc.contMDiffAt (hU.mem_nhds (hmap hy))).mdifferentiableAt (by simp))
        ((hk.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) hgerm v w
    · intro y hy
      have hgerm : (event.limit_identify.map ∘ c.symm) ∘ k =ᶠ[𝓝 y]
          event.limit_identify.map ∘ A := by
        filter_upwards [hW.mem_nhds hy] with z hz
        exact congrArg event.limit_identify.map (hfactor z hz).symm
      ext v w
      exact event.limit_metric.pullbackCoefficients_eq_of_comp_germ
        ((hf.contMDiffAt (hU.mem_nhds (hmap hy))).mdifferentiableAt (by simp))
        ((hk.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) hgerm v w
  exact (hactual.jets j {x} isCompact_singleton (singleton_subset_iff.mpr hxW)).tendsto_at
    (mem_singleton x)

theorem tendsto_preterminal_pullback_twoJet
    (event : SurgeryEventData g0 K P slice metric T)
    {A : E → (slice event.tMinus).carrier} {V : Set E} (hV : IsOpen V)
    (hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V)
    (hregular : MapsTo A V event.regular_limit) {x : E} (hx : x ∈ V) :
    Tendsto (fun t => metricTwoJet ((event.pre_flow.metric t).pullbackCoefficients A) x)
      (𝓝[<] T) (𝓝 (metricTwoJet (event.limit_metric.pullbackCoefficients
        (event.limit_identify.map ∘ A)) x)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hj (j : ℕ) : ∀ᶠ t in 𝓝[<] T,
      ‖iteratedFDeriv ℝ j ((event.pre_flow.metric t).pullbackCoefficients A) x -
        iteratedFDeriv ℝ j (event.limit_metric.pullbackCoefficients
          (event.limit_identify.map ∘ A)) x‖ ≤ eta / 2 := by
    have h := Metric.tendsto_nhds.mp
      (tendsto_preterminal_pullback_jet event hV hA hregular hx j) (eta / 2) (half_pos heta)
    filter_upwards [h] with t ht
    exact (by simpa only [dist_eq_norm] using ht :
      ‖iteratedFDeriv ℝ j ((event.pre_flow.metric t).pullbackCoefficients A) x -
        iteratedFDeriv ℝ j (event.limit_metric.pullbackCoefficients
          (event.limit_identify.map ∘ A)) x‖ < eta / 2).le
  filter_upwards [hj 0, hj 1, hj 2] with t h0 h1 h2
  rw [dist_eq_norm]
  apply (norm_metricTwoJet_sub_le _ _ x ?_).trans_lt (half_lt_self heta)
  intro j hj
  interval_cases j <;> assumption

end PoincareConjecture.M44

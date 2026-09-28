import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourcePositiveBoundedRegularity
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSuffix
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallStrongRadius
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.PathCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1200000 in

theorem exists_retained_short_suffix_capture_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (_D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (L : EpsilonNeck G.limitMetric) (j : ℕ), L.center = G.base →
            L.carrier ⊆ G.exhaustion j →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ᶠ k in atTop, (G.embedding (sigma k) q).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ ell : ℕ, ∀ᶠ k in atTop, ell ≤ sigma k ∧ j ≤ sigma k ∧
                ∃ a ∈ L.central_sphere,
                  ∃ gamma : ℝ → H.tubeCriticalRegion W.tube W.radius
                    (W.high_index (G.subsequence (sigma k))),
                    gamma 0 = G.embedding (sigma k) a ∧
                    gamma 1 = G.embedding (sigma k) q ∧
                    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1) ∧
                    MapsTo gamma (Icc (0 : ℝ) 1)
                      (G.embedding (sigma k) '' G.exhaustion ell) ∧
                    (H.tubeCriticalMetric W.tube W.radius
                      (W.high_index (G.subsequence (sigma k)))).pathELength gamma 0 1 <
                        ENNReal.ofReal W.radius := by
  classical

  have hA := exists_retained_strong_neck_radial_margin_accuracy.{u} P
  let epsilonA := hA.choose
  have hApos : 0 < epsilonA := hA.choose_spec.1
  have hAsmall := hA.choose_spec.2.1
  have hRegExists := exists_source_positive_bounded_regular_accuracy.{u} P
  let epsilonB := hRegExists.choose
  have hBpos : 0 < epsilonB := hRegExists.choose_spec.1
  refine ⟨min epsilonA epsilonB, lt_min hApos hBpos,
    (min_le_left _ _).trans hAsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L j hLcenter hLstage sigma hsigma f hf hbound hgraphs hside
  have hJ := hA.choose_spec.2.2 H W (hepsilon.trans (min_le_left _ _))
    G D0 q L hLcenter sigma hsigma f hf hbound hgraphs hside
  let J := hJ.choose
  have hcenter := hJ.choose_spec.1
  have hEta := hJ.choose_spec.2.2.2
  let eta := hEta.choose
  have heta : 0 < eta := hEta.choose_spec.1
  have hetaR : eta < W.radius := hEta.choose_spec.2.1
  have hmargin := hEta.choose_spec.2.2
  let r := W.radius - eta / 2
  have hr : 0 < r := by dsimp [r]; linarith only [hetaR, heta]
  have hrR : r < W.radius := by dsimp [r]; linarith only [heta]
  have hScalar := W.radius_bound r hrR
  let B0 := hScalar.choose
  have hB0 := hScalar.choose_spec
  let B := max B0 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRegular := hRegExists.choose_spec.2.2 H W.tube
    (hepsilon.trans (min_le_right _ _)) W.radius r B hr hrR hB
  let delta := hRegular.choose
  have hdelta : 0 < delta := hRegular.choose_spec.1
  have hreg := hRegular.choose_spec.2
  have hStage := G.exists_eventually_regular_path_capture j delta hdelta
  let ell := hStage.choose
  have hcapture := hStage.choose_spec
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  have hnu : StrictMono nu := W.high_index_strictMono.comp
    (G.subsequence_strictMono.comp hsigma)
  have heps : 0 < epsilon := (W.tube 0).epsilon_eq ▸ (W.tube 0).tube.epsilon_pos
  have hhalf : epsilon < 1 / 2 :=
    ((hepsilon.trans (min_le_left _ _)).trans hAsmall).trans_lt (by norm_num)
  have htail := hmargin.and (hside.and
    ((hnu.tendsto_atTop.eventually hB0).and
      ((hnu.tendsto_atTop.eventually hreg).and
        ((hsigma.tendsto_atTop.eventually hcapture).and
          (hsigma.tendsto_atTop.eventually (eventually_ge_atTop j))))))
  refine ⟨ell, htail.mono ?_⟩
  intro k hk
  have hkmargin := hk.1
  have hkside := hk.2.1
  have hkB := hk.2.2.1
  have hkreg := hk.2.2.2.1
  have hkcap := hk.2.2.2.2.1
  have hkj := hk.2.2.2.2.2
  let gk := H.tubeCriticalMetric W.tube W.radius (nu k)
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : H.tubeCriticalRegion W.tube W.radius (nu k) → Type _) :=
    ⟨gk.toRiemannianMetric⟩
  let N := strongNeck_top (J k) hhalf
  have hzero : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp N.center_on_central_sphere
  have hcenterMargin := hkmargin N.center
    (N.central_sphere_subset N.center_on_central_sphere)
    (by change |(N.coordinate_inverse N.center).2| ≤ 3 * epsilon⁻¹ / 4
        rw [hzero, abs_zero]
        positivity)
  have hxrad := hcenterMargin.choose_spec
  have hqrad : ((H.tubeMetric W.tube (nu k)).edist
      (H.tubeBase W.tube (nu k)) (G.embedding (sigma k) q).val).toReal <
        W.radius - eta := by
    have heq : (⟨N.center, hcenterMargin.choose⟩ : (W.tube (nu k)).carrierOpen) =
        (G.embedding (sigma k) q).val := Subtype.ext (hcenter k)
    rw [heq] at hxrad
    exact hxrad
  have hqdist : gk.edist (H.tubeCriticalBase W.tube W.radius W.radius_pos (nu k))
      (G.embedding (sigma k) q) < ENNReal.ofReal r := by
    rw [H.tubeCritical_base_edist W.tube W.radius W.radius_pos]
    rw [← ENNReal.ofReal_toReal (H.tube_edist_ne_top W.tube (nu k) _ _)]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    dsimp only [r]
    linarith only [hqrad, heta]
  have hshort := Manifold.exists_lt_of_riemannianEDist_lt hqdist
  let gamma := hshort.choose
  have h0 : gamma 0 = H.tubeCriticalBase W.tube W.radius W.radius_pos (nu k) :=
    hshort.choose_spec.1
  have h1 : gamma 1 = G.embedding (sigma k) q := hshort.choose_spec.2.1
  have hgamma := hshort.choose_spec.2.2.1
  have hlength := hshort.choose_spec.2.2.2
  have hball : MapsTo gamma (Icc (0 : ℝ) 1)
      (gk.ball (H.tubeCriticalBase W.tube W.radius W.radius_pos (nu k)) r) := by
    have hh : MapsTo gamma (Icc (0 : ℝ) 1) (gk.ball (gamma 0) r) :=
      gk.mapsTo_ball_of_pathELength_lt hgamma hlength
    rwa [h0] at hh
  have hrad (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (gamma t).val ∈ (H.tubeMetric W.tube (nu k)).ball (H.tubeBase W.tube (nu k)) r := by
    have hh := hball ht
    rw [H.tubeCritical_ball_eq_preimage W.tube W.radius W.radius_pos (nu k) hrR.le] at hh
    exact hh
  let raw : ℝ → ((E (nu k + H.shift)).flow.slice (E (nu k + H.shift)).time).carrier :=
    fun t => (gamma t).val.val
  have hraw : ContinuousOn raw (Icc (0 : ℝ) 1) :=
    continuous_subtype_val.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hgamma.continuousOn)
  have hbaseGraph : raw 0 ∈ range (fun z =>
      ((W.tube (nu k)).list.node 0).2.coordinate_map (z, f k z)) := by
    rw [← hgraphs k]
    refine ⟨G.base, hLcenter ▸ L.center_on_central_sphere, ?_⟩
    change (G.embedding (sigma k) G.base).val.val = (gamma 0).val.val
    exact congrArg
      (fun x : H.tubeCriticalRegion W.tube W.radius (nu k) => x.val.val)
      ((G.base_preserving (sigma k)).trans h0.symm)
  have hfinal :=
    (W.tube (nu k)).exists_final_initial_graph_subarc (f k) (hf k).continuous (hbound k)
      zero_le_one hraw (fun v _ => (gamma v).val.property) hbaseGraph
      (by simpa only [raw, h1] using hkside)
  let t := hfinal.choose
  have ht := hfinal.choose_spec.1
  have htGraph := hfinal.choose_spec.2.1
  have hafter := hfinal.choose_spec.2.2
  have hstart : raw t ∈
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k)) '' L.central_sphere := by
    rwa [hgraphs k]
  let a := hstart.choose
  have ha := hstart.choose_spec.1
  have hrawa := hstart.choose_spec.2
  have haeq : gamma t = G.embedding (sigma k) a :=
    Subtype.ext (Subtype.ext hrawa.symm)
  have hsub : Icc t 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht.1 le_rfl
  have hregularSuffix : MapsTo gamma (Icc t 1) (regularPoints gk delta) := by
    intro v hv
    apply hkreg (f k) (hf k).continuous (hbound k) (gamma v) (hrad v (hsub hv))
    · have hh := hkB (gamma v).val (ENNReal.toReal_lt_of_lt_ofReal (hrad v (hsub hv)))
      change (H.tubeConnection W.tube (nu k)).scalarCurvature (gamma v).val ≤ B0 at hh
      rw [H.tube_scalar_eq] at hh
      exact hh.trans (le_max_left _ _)
    · exact hafter hv
  have hcaptured : MapsTo gamma (Icc t 1)
      (G.embedding (sigma k) '' G.exhaustion ell) :=
    hkcap.2 gamma t 1 ht.2 (hgamma.continuousOn.mono hsub) hregularSuffix
      ⟨a, hLstage (L.central_sphere_subset ha), haeq.symm⟩
  have hunit := exists_unit_interval_path gk ht.2 (hgamma.mono hsub) hcaptured
  let beta := hunit.choose
  have hb0 := hunit.choose_spec.1
  have hb1 := hunit.choose_spec.2.1
  have hbeta := hunit.choose_spec.2.2.1
  have hbetaImage := hunit.choose_spec.2.2.2.1
  have hbetaLength := hunit.choose_spec.2.2.2.2
  refine ⟨hkcap.1, hkj, a, ha, beta, hb0.trans haeq, hb1.trans h1,
    hbeta, hbetaImage, ?_⟩
  rw [hbetaLength]
  exact ((Manifold.pathELength_mono ht.1 le_rfl).trans_lt hlength).trans_le
    (ENNReal.ofReal_le_ofReal hrR.le)

end PoincareConjecture.M28.CounterexampleNeckFamily

import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CornerPartition
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryDensity
import PoincareConjecture.Proofs.M08.PathGluing










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem oneCorner_contMDiffAt {a c b s : ℝ} {gamma : ℝ → G.Point}
    (hleft : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc a c))
    (hright : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc c b))
    (hs : s ∈ Ioo a b) (hsc : s ≠ c) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma s := by
  rcases lt_or_gt_of_ne hsc with hsc | hcs
  · exact (hleft s ⟨hs.1.le, hsc.le⟩).contMDiffAt (Icc_mem_nhds hs.1 hsc)
  · exact (hright s ⟨hcs.le, hs.2.le⟩).contMDiffAt (Icc_mem_nhds hcs hs.2)

set_option synthInstance.maxHeartbeats 200000 in



theorem oneCorner_gauge_action_eq (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {a c b : ℝ} (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hleft : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc a c))
    (hright : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc c b))
    (R : GaugePrimitivePartition gamma a b)
    (hvelocity : ∀ i, (R.velocity i : ℝ → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Icc (R.node i.castSucc) (R.node i.succ))]
        deriv (fun s => ((R.gauge i).lift (gamma s)).2.val)) :
    IntervalIntegrable (M14.squareCurveDensity G gamma (Icc a b)) volume a b ∧
      R.action = ∫ s in a..b, M14.squareCurveDensity G gamma (Icc a b) s := by
  let D := M14.squareCurveDensity G gamma (Icc a b)
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth.continuous
  have hV : Continuous (fun s => 2 * s ^ 2 *
      horizontalScalarCurvature G.leafwise (gamma s)) :=
    (continuous_const.mul (continuous_id.pow 2)).mul (hscalar.comp hgamma)
  have hpiece (i : Fin R.count) :
      IntervalIntegrable D volume (R.node i.castSucc) (R.node i.succ) ∧
      gaugePieceAction (R.gauge i) gamma (R.velocity i) =
        ∫ s in R.node i.castSucc..R.node i.succ, D s := by
    let e := R.gauge i
    let l := R.node i.castSucc
    let r := R.node i.succ
    have hlr : l ≤ r := R.monotone (Fin.castSucc_le_succ i)
    have hsub : Icc l r ⊆ Icc a b :=
      Icc_subset_Icc (R.first ▸ R.monotone (Fin.zero_le _))
        (R.last ▸ R.monotone (Fin.le_last _))
    have hsrc : MapsTo gamma (Icc l r) e.source :=
      fun _ hs => R.source i (R.core_subset i hs)
    let B s := (1 / 2 : ℝ) • gaugeLiftMetric e.index e.lift e.center (gamma s)
    let Q s := B s (R.velocity i s) (R.velocity i s)
    let V s := 2 * s ^ 2 * horizontalScalarCurvature G.leafwise (gamma s)
    have hB : ContinuousOn B (Icc l r) :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc l r)).smul
        ((gaugeLiftMetric_continuousOn e.index e.lift e.center e.smooth).comp
          hgamma.continuousOn hsrc)
    have hBLp : MemLp B ⊤ (volume.restrict (Icc l r)) :=
      M08.continuousOn_memLp_top_Icc (f := B) (a := l) (b := r) hB
    have hQ : IntervalIntegrable Q volume l r :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mpr
        (M08.chart_density_integrable B hBLp (R.velocity i))
    have hVint : IntervalIntegrable V volume l r := hV.intervalIntegrable _ _
    have heq : D =ᵐ[volume.restrict (Icc l r)] fun s => Q s + V s := by
      have hmem : ∀ᵐ s ∂volume.restrict (Icc l r), s ∈ Ioo l r := by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hvelocity i, hmem, (volume.restrict (Icc l r)).ae_ne c]
        with s hv hs hsc
      have hsab : s ∈ Ioo a b :=
        ⟨(hsub ⟨le_rfl, hlr⟩).1.trans_lt hs.1,
          hs.2.trans_le (hsub ⟨hlr, le_rfl⟩).2⟩
      have hg := oneCorner_contMDiffAt hleft hright hsab hsc
      have hlift := (e.smooth.contMDiffAt (e.source_open.mem_nhds
        (hsrc (Ioo_subset_Icc_self hs)))).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
      have hpair := hlift.comp s hg
      have hrec : gamma =ᶠ[𝓝 s] fun z =>
          (G.gaugeCover.cylinder e.index).toSpacetime
            ((e.lift (gamma z)).1, (e.lift (gamma z)).2) := by
        filter_upwards [Icc_mem_nhds hs.1 hs.2] with z hz
        exact (e.right_inv (gamma z) (hsrc hz)).symm
      have hden := square_density_gauge_germ e.index
        (fun z => (e.lift (gamma z)).1) (fun z => (e.lift (gamma z)).2) gamma
        (Icc_mem_nhds hsab.1 hsab.2) hrec
        (hpair.fst.mdifferentiableAt (by simp)) (hpair.snd.mdifferentiableAt (by simp))
      dsimp only [D]
      rw [hden]
      dsimp only [Q, B, V]
      rw [hv, smul_apply, smul_apply, smul_eq_mul, gaugeLiftMetric_apply]
      rw [e.right_inv (gamma s) (hsrc (Ioo_subset_Icc_self hs))]
      exact add_comm _ _
    have heqI : D =ᵐ[volume.restrict (uIoc l r)] fun s => Q s + V s := by
      rw [uIoc_of_le hlr]
      exact ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) heq
    refine ⟨(hQ.add hVint).congr_ae heqI.symm, ?_⟩
    change (∫ s in l..r, Q s) + (∫ s in l..r, V s) = ∫ s in l..r, D s
    rw [← intervalIntegral.integral_add hQ hVint]
    exact intervalIntegral.integral_congr_ae_restrict heqI.symm
  have hsum := M08.integrable_sum_fin_partition R.node D (fun i => (hpiece i).1)
  refine ⟨?_, ?_⟩
  · simpa only [R.first, R.last] using hsum.1
  · unfold GaugePrimitivePartition.action
    simp_rw [(hpiece _).2]
    simpa only [R.first, R.last] using hsum.2

end PoincareConjecture.Proofs.M46

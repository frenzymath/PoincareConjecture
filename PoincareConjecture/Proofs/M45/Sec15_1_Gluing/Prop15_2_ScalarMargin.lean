import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_FourJetControl
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_ScalarReadout
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CoefficientGerms
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_ScalarEvolution
import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderMargin
import PoincareConjecture.Proofs.M04.ScalarEstimates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance : NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace
noncomputable local instance : NormedAddCommGroup (ScalarMetricFourJet 3) := Prod.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (ScalarMetricFourJet 3) := Prod.normedSpace




theorem exists_recent_scalar_margin :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 4 ∧
      ∀ {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta),
      0 < beta * epsilon → beta * epsilon ≤ eta0 → I.recent_duration < 1 →
      ∀ t ∈ Icc (-I.recent_duration) (0 : ℝ),
        (1 / 4 : ℝ) < (I.recent_flow.connection t).scalarCurvature I.center ∧
          |(I.recent_flow.connection t).laplacian
            (I.recent_flow.connection t).scalarCurvature I.center| < (1 / 100 : ℝ) := by
  obtain ⟨delta, hdelta, hmargin⟩ := exists_uniform_evolvingCylinder_scalar_margin
  obtain ⟨C, hC, herror⟩ := exists_evolvingCylinder_fourJet_error
  let eta0 := min (1 / 4) (delta / C)
  have heta0 : 0 < eta0 := lt_min (by norm_num) (div_pos hdelta hC)
  refine ⟨eta0, heta0, min_le_left _ _, ?_⟩
  intro epsilon beta I hpos hsmall hduration t ht
  have hquarter : beta * epsilon ≤ 1 / 4 := hsmall.trans (min_le_left _ _)
  have hhalf : beta * epsilon < 1 / 2 := lt_of_le_of_lt hquarter (by norm_num)
  have hfour : 4 ≤ ⌊(beta * epsilon)⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hpos).mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hquarter]
  have htime : t ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨q, hq⟩ := I.recent_patch.center_sphere
  let z : RoundCylinderSpace := (q, 0)
  have hz : z.2 ∈ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹ := by
    exact ⟨neg_lt_zero.mpr (inv_pos.mpr hpos), inv_pos.mpr hpos⟩
  let N := I.recentNeck hpos hhalf
  let A := I.recentCenteredMap z
  let U := centeredNeckDomain N 0
  have hU : IsOpen U := centeredNeckDomain_isOpen N 0
  have hzero : (0 : E) ∈ U := zero_mem_centeredNeckDomain N hz
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A U :=
    fun p hp => (centeredNeckLift_contMDiffAt N q 0 hp).contMDiffWithinAt
  have hi (p : E) (hp : p ∈ U) : (mfderiv (𝓡 3) (𝓡 3) A p).IsInvertible :=
    centeredNeckLift_mfderiv_isInvertible N q 0 hp
  have hA0 : A 0 = I.center := by
    change I.recent_patch.coordinate (centeredCylinderLift q 0 0) = I.center
    rw [centeredCylinderLift_zero]
    exact hq
  let B := roundCylinderPullback (I.recent_flow.metric t) I.recent_patch.coordinate
  have hB : RoundCylinderClose (beta * epsilon) t B := by
    obtain ⟨hs, bound, hbound, hjets⟩ := I.recent_comparison
    exact ⟨hs t ht, bound, hbound, hjets t ht⟩
  have hnear : ‖scalarMetricFourJet (centeredCylinderMetric B z.1 z.2) 0 -
      scalarMetricFourJet (evolvingCylinderModelField t) 0‖ ≤ delta := by
    apply (herror hpos htime hB hfour z hz).trans
    have he := (le_div_iff₀ hC).mp (hsmall.trans (min_le_right _ _))
    nlinarith only [he]
  obtain ⟨_, hscalar, hlap⟩ := hmargin t htime _ hnear
  have hcoeff : (I.recent_flow.metric t).pullbackCoefficients A =ᶠ[𝓝 (0 : E)]
      centeredCylinderMetric B z.1 z.2 := by
    filter_upwards [hU.mem_nhds hzero] with p hp
    exact I.recentCenteredMap_pullbackCoefficients hpos hhalf z t hp
  have hS := jetScalarCurvature_pullbackCoefficients
    (I.recent_flow.metric t) (I.recent_flow.connection t) hU hA hi hzero
  rw [(metricTwoJet_eventuallyEq hcoeff).self_of_nhds, hA0] at hS
  have hL := jetScalarLaplacian_pullbackCoefficients
    (I.recent_flow.metric t) (I.recent_flow.connection t) hU hA hi hzero
  rw [scalarMetricFourJet_congr hcoeff, hA0] at hL
  exact ⟨by simpa only [scalarMetricFourJet, hS] using hscalar,
    by simpa only [hL] using hlap⟩




theorem exists_short_input_scale_bounds :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 4 ∧
      ∀ {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta),
      0 < beta * epsilon → beta * epsilon ≤ eta0 → I.recent_duration < 1 →
      (1 / 4 : ℝ) < (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center ∧
        (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center < 1 ∧
        1 < I.older_neck.neck.scale ^ 2 ∧ I.older_neck.neck.scale ^ 2 < 4 ∧
        1 < I.older_duration := by
  obtain ⟨eta0, heta0, hquarter, hmargin⟩ := exists_recent_scalar_margin.{u}
  refine ⟨eta0, heta0, hquarter, ?_⟩
  intro epsilon beta I hpos hsmall hduration
  have hevolution : ∀ t ∈ Ioo (-I.recent_duration) (0 : ℝ),
      0 < (I.recent_flow.connection t).laplacian
        (I.recent_flow.connection t).scalarCurvature I.center +
          2 * (I.recent_flow.connection t).ricciNormSq I.center := by
    intro t ht
    obtain ⟨hR, hL⟩ := hmargin I hpos hsmall hduration t ⟨ht.1.le, ht.2.le⟩
    have htrace := (I.recent_flow.connection t).scalarCurvature_sq_le I.center
    have hLlo := (abs_lt.mp hL).1
    norm_num only [Nat.cast_ofNat] at htrace
    nlinarith [sq_nonneg ((I.recent_flow.connection t).scalarCurvature I.center - 1 / 4)]
  have hq := (hmargin I hpos hsmall hduration (-I.recent_duration)
    ⟨le_rfl, by linarith [I.recent_duration_pos]⟩).1
  have hqpos : 0 < (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center :=
    lt_trans (by norm_num) hq
  have hqone := I.joining_scalar_lt_one_of_evolution_pos hevolution
  refine ⟨hq, hqone, ?_, ?_, I.older_duration_gt_one_of_evolution_pos hevolution⟩
  · rw [I.older_scale_sq]
    simpa only [inv_one] using inv_strictAnti₀ hqpos hqone
  · rw [I.older_scale_sq]
    have h := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 4) hq
    norm_num at h ⊢
    exact h

end PoincareConjecture.M45

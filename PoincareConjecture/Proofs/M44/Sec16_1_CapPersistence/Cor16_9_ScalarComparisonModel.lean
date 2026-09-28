import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_StandardSphereMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialChartBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance scalarModelCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarModelCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance scalarModelTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance scalarModelTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem exists_global_standard_scalar_bound {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc (0 : ℝ) H, ∀ x : E,
      (S.flow.connection t).scalarCurvature x ≤ M := by
  obtain ⟨K, hK, hcurv⟩ := S.flow.base.curvature_locally_bounded H hH0
    (by rwa [S.lifetime_one])
  refine ⟨9 * K + 1, by positivity, ?_⟩
  intro t ht x
  have hscalar := abs_scalar_le_curvatureTensorNorm (S.flow.connection t) x
  norm_num at hscalar
  have hnorm := (le_abs_self _).trans (hcurv t ht x)
  calc
    _ ≤ |(S.flow.connection t).scalarCurvature x| := le_abs_self _
    _ ≤ 9 * (S.flow.connection t).curvatureTensorNorm x := hscalar
    _ ≤ 9 * K := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ ≤ 9 * K + 1 := by linarith




theorem exists_uniform_scalar_jet_upper_margin {C : Set (MetricTwoJet 3)}
    (hC : IsCompact C) {M : ℝ}
    (hinv : ∀ J ∈ C, J.1.IsInvertible)
    (hbound : ∀ J ∈ C, jetScalarCurvature J ≤ M) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ C, ∀ J' : MetricTwoJet 3,
      ‖J' - J‖ ≤ delta → jetScalarCurvature J' < M + 1 := by
  let U : Set (MetricTwoJet 3) :=
    {J | J.1.IsInvertible ∧ jetScalarCurvature J < M + 1}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro J hJ
    have hi := (isOpen_ricciFlowOperator_domain 3).mem_nhds hJ.1
    have hs := (contDiffAt_jetScalarCurvature hJ.1).continuousAt.eventually
      (gt_mem_nhds hJ.2)
    filter_upwards [hi, hs] with J' hI hS
    exact ⟨hI, hS⟩
  have hCU : C ⊆ U := fun J hJ =>
    ⟨hinv J hJ, (hbound J hJ).trans_lt (lt_add_one M)⟩
  obtain ⟨delta, hdelta, hinside⟩ := hC.exists_cthickening_subset_open hU hCU
  refine ⟨delta, hdelta, ?_⟩
  intro J hJ J' hnear
  exact (hinside (Metric.mem_cthickening_of_dist_le J' J delta C hJ
    (by simpa only [dist_eq_norm] using hnear))).2





theorem exists_standard_scalar_comparison_tolerance {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {H M : ℝ} (hH1 : H < 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) H, ∀ x : E,
      (S.flow.connection t).scalarCurvature x ≤ M)
    {C : Set E} (hC : IsCompact C) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc (0 : ℝ) H, ∀ x ∈ C,
      ∀ J : MetricTwoJet 3,
        ‖J - metricTwoJet (S.flow.metric t).euclideanCoefficients x‖ ≤ delta →
          jetScalarCurvature J < M + 1 := by
  let jet : ℝ × E → MetricTwoJet 3 := fun p =>
    metricTwoJet (S.flow.metric p.1).euclideanCoefficients p.2
  have hsub : Icc (0 : ℝ) H ⊆ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt hH1⟩
  have hcont : ContinuousOn jet (Icc (0 : ℝ) H ×ˢ C) :=
    (continuousOn_euclidean_twoJet (uniqueDiffOn_Ico 0 S.flow.base.lifetime)
      S.flow.base.flow).mono (prod_mono hsub (subset_univ C))
  have hcompact : IsCompact (jet '' (Icc (0 : ℝ) H ×ˢ C)) :=
    (isCompact_Icc.prod hC).image_of_continuousOn hcont
  obtain ⟨delta, hdelta, hmargin⟩ := exists_uniform_scalar_jet_upper_margin hcompact
    (M := M) (by
      rintro _ ⟨p, _hp, rfl⟩
      exact (S.flow.metric p.1).inner_isInvertible p.2) (by
      rintro _ ⟨p, hp, rfl⟩
      change jetScalarCurvature (metricTwoJet
        (S.flow.metric p.1).euclideanCoefficients p.2) ≤ M
      rw [jetScalarCurvature_metricTwoJet (S.flow.connection p.1)]
      exact hbound p.1 hp.1 p.2)
  exact ⟨delta, hdelta, fun t ht x hx J hnear =>
    hmargin (jet (t, x)) (mem_image_of_mem jet ⟨ht, hx⟩) J hnear⟩

end PoincareConjecture.M44

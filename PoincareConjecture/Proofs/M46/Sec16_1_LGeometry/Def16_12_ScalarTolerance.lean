import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_StandardSphereMargin
import PoincareConjecture.Proofs.M44.StandardScalar

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "Jet" => MetricTwoJet 3

noncomputable local instance scalarToleranceCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarToleranceCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance scalarToleranceTwoJetNorm :
    NormedAddCommGroup Jet := Prod.normedAddCommGroup

noncomputable local instance scalarToleranceTwoJetSpace :
    NormedSpace ℝ Jet := Prod.normedSpace

theorem exists_uniform_scalarJet_error {C : Set Jet} (hC : IsCompact C)
    (hinv : ∀ J ∈ C, J.1.IsInvertible) {error : ℝ} (herror : 0 < error) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ C, ∀ J' : Jet,
      ‖J' - J‖ ≤ delta → |M44.jetScalarCurvature J' - M44.jetScalarCurvature J| < error := by
  let diagonal : Set (Jet × Jet) := (fun J => (J, J)) '' C
  let U : Set (Jet × Jet) := {p | p.1.1.IsInvertible ∧ p.2.1.IsInvertible ∧
    |M44.jetScalarCurvature p.2 - M44.jetScalarCurvature p.1| < error}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hi1 := ((isOpen_ricciFlowOperator_domain 3).preimage continuous_fst).mem_nhds hp.1
    have hi2 := ((isOpen_ricciFlowOperator_domain 3).preimage continuous_snd).mem_nhds hp.2.1
    have hc1 := (M44.contDiffAt_jetScalarCurvature hp.1).continuousAt.comp
      continuous_fst.continuousAt
    have hc2 := (M44.contDiffAt_jetScalarCurvature hp.2.1).continuousAt.comp
      continuous_snd.continuousAt
    have he := (hc2.sub hc1).abs.eventually (gt_mem_nhds hp.2.2)
    filter_upwards [hi1, hi2, he] with p' h1 h2 hdiff
    exact ⟨h1, h2, hdiff⟩
  have hdiagonal : IsCompact diagonal := hC.image (continuous_id.prodMk continuous_id)
  have hsubset : diagonal ⊆ U := by
    rintro _ ⟨J, hJ, rfl⟩
    exact ⟨hinv J hJ, hinv J hJ, by simpa only [sub_self, abs_zero] using herror⟩
  obtain ⟨delta, hdelta, hinside⟩ := hdiagonal.exists_cthickening_subset_open hU hsubset
  refine ⟨delta, hdelta, ?_⟩
  intro J hJ J' hnear
  have hdist : dist (J, J') (J, J) ≤ delta := by
    change max (dist J J) (dist J' J) ≤ delta
    rw [dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact hnear
  exact (hinside (Metric.mem_cthickening_of_dist_le (J, J') (J, J) delta
    diagonal (mem_image_of_mem _ hJ) hdist)).2.2

theorem exists_standardCap_scalarRate_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {c theta : ℝ}
    (hc : 0 < c) (htheta : theta < 1)
    (hrate : ∀ t ∈ Ico 0 P.standard_cap.flow.base.lifetime, ∀ x : E,
      c / (1 - t) ≤ (P.standard_cap.flow.connection t).scalarCurvature x)
    {C : Set E} (hC : IsCompact C) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc 0 theta, ∀ x ∈ C,
      ∀ J : Jet,
        ‖J - metricTwoJet (P.standard_cap.flow.metric t).euclideanCoefficients x‖ ≤ delta →
        c / (2 * (1 - t)) ≤ M44.jetScalarCurvature J := by
  let jets : ℝ × E → Jet := fun p =>
    metricTwoJet (P.standard_cap.flow.metric p.1).euclideanCoefficients p.2
  have hsub : Icc (0 : ℝ) theta ⊆ Ico 0 P.standard_cap.flow.base.lifetime := by
    rw [P.standard_cap.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt htheta⟩
  have hcont : ContinuousOn jets (Icc (0 : ℝ) theta ×ˢ C) :=
    (M44.continuousOn_euclidean_twoJet
      (uniqueDiffOn_Ico 0 P.standard_cap.flow.base.lifetime)
      P.standard_cap.flow.base.flow).mono (prod_mono hsub (subset_univ C))
  have hcompact : IsCompact (jets '' (Icc (0 : ℝ) theta ×ˢ C)) :=
    (isCompact_Icc.prod hC).image_of_continuousOn hcont
  obtain ⟨delta, hdelta, hbound⟩ := exists_uniform_scalarJet_error hcompact
    (by
      rintro _ ⟨p, _hp, rfl⟩
      exact (P.standard_cap.flow.metric p.1).inner_isInvertible p.2)
    (show 0 < c / 2 by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro t ht x hx J hnear
  have herr := hbound (jets (t, x)) (mem_image_of_mem _ ⟨ht, hx⟩) J hnear
  change |M44.jetScalarCurvature J -
    M44.jetScalarCurvature (metricTwoJet
      (P.standard_cap.flow.metric t).euclideanCoefficients x)| < c / 2 at herr
  rw [M44.jetScalarCurvature_metricTwoJet (P.standard_cap.flow.connection t)] at herr
  have hmodel := hrate t (hsub ht) x
  have hden : 0 < 1 - t := sub_pos.mpr (ht.2.trans_lt htheta)
  have hhalf : c / 2 ≤ c / (2 * (1 - t)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) hden)).mpr
    nlinarith [ht.1]
  have hsplit : c / (1 - t) = 2 * (c / (2 * (1 - t))) := by
    field_simp
  linarith [(abs_lt.mp herr).1]

end PoincareConjecture.Proofs.M46

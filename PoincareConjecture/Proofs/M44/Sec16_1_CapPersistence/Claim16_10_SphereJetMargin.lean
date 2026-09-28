import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StandardCollar












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance sphereCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sphereCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance sphereTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance sphereTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace



def sectionalJetLowerRegion (k : ℝ) (u v : E) : Set (MetricTwoJet 3) :=
  {J | J.1.IsInvertible ∧ 0 < collarJetGram u v J ∧
    k * collarJetGram u v J < jetCurvature J u v u v}



theorem isOpen_sectionalJetLowerRegion (k : ℝ) (u v : E) :
    IsOpen (sectionalJetLowerRegion k u v) := by
  rw [isOpen_iff_mem_nhds]
  intro J hJ
  have hinv := (isOpen_ricciFlowOperator_domain 3).mem_nhds hJ.1
  have hgram := (continuous_collarJetGram u v).continuousAt.eventually
    (lt_mem_nhds hJ.2.1)
  have hpositive : ∀ᶠ K in 𝓝 J,
      0 < jetCurvature K u v u v - k * collarJetGram u v K :=
    ((contDiffAt_jetCurvature hJ.1 u v u v).continuousAt.sub
      (continuousAt_const.mul (continuous_collarJetGram u v).continuousAt)).eventually
        (lt_mem_nhds (sub_pos.mpr hJ.2.2))
  filter_upwards [hinv, hgram, hpositive] with K hI hG hP
  exact ⟨hI, hG, sub_pos.mp hP⟩



theorem exists_uniform_sectional_jet_lower_margin (k : ℝ) (u v : E)
    {K : Set (MetricTwoJet 3)} (hK : IsCompact K)
    (hsub : K ⊆ sectionalJetLowerRegion k u v) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ K, ∀ J' : MetricTwoJet 3,
      ‖J' - J‖ ≤ delta → J' ∈ sectionalJetLowerRegion k u v := by
  obtain ⟨delta, hdelta, hinside⟩ :=
    hK.exists_cthickening_subset_open (isOpen_sectionalJetLowerRegion k u v) hsub
  refine ⟨delta, hdelta, ?_⟩
  intro J hJ J' hnear
  exact hinside (Metric.mem_cthickening_of_dist_le J' J delta K hJ
    (by simpa only [dist_eq_norm] using hnear))



theorem evolvingCylinderModelJet_horizontalGram (t : ℝ) :
    collarJetGram (e 0) (e 1) (evolvingCylinderModelJet t) = (2 * (1 - t)) ^ 2 := by
  unfold collarJetGram
  change evolvingCylinderModelField t 0 (e 0) (e 0) *
      evolvingCylinderModelField t 0 (e 1) (e 1) -
        (evolvingCylinderModelField t 0 (e 0) (e 1)) ^ 2 = _
  rw [evolvingCylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    cylinderHorizontalForm_basis, cylinderHeightCovector_basis]
  simp [cylinderHorizontalGram, roundCylinderCoordinateBasis, pow_two,
    EuclideanSpace.inner_single_left]



theorem evolvingCylinderModelJet_horizontalCurvature (t : ℝ) :
    jetCurvature (evolvingCylinderModelJet t) (e 0) (e 1) (e 0) (e 1) = 2 * (1 - t) := by
  rw [jetCurvature_evolvingCylinderModelJet]
  simp only [cylinderHorizontalForm_basis]
  simp [cylinderHorizontalGram, roundCylinderCoordinateBasis,
    EuclideanSpace.inner_single_left]



theorem evolvingCylinderModelJet_mem_sphereRegion {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    evolvingCylinderModelJet t ∈ sectionalJetLowerRegion (1 / 4) (e 0) (e 1) := by
  refine ⟨evolvingCylinderModelJet_isInvertible ht, ?_, ?_⟩
  · rw [evolvingCylinderModelJet_horizontalGram]
    exact sq_pos_of_pos (by linarith)
  · rw [evolvingCylinderModelJet_horizontalGram, evolvingCylinderModelJet_horizontalCurvature]
    have hmul := mul_nonneg ht0 (sub_pos.mpr ht).le
    nlinarith



theorem exists_evolvingCylinder_sphere_tolerance {theta : ℝ} (htheta : theta < 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc (0 : ℝ) theta, ∀ J : MetricTwoJet 3,
      ‖J - evolvingCylinderModelJet t‖ ≤ delta →
        J ∈ sectionalJetLowerRegion (1 / 4) (e 0) (e 1) := by
  obtain ⟨delta, hdelta, hmargin⟩ :=
    exists_uniform_sectional_jet_lower_margin (1 / 4) (e 0) (e 1)
      (isCompact_Icc.image continuous_evolvingCylinderModelJet)
      (by
        rintro J ⟨t, ht, rfl⟩
        exact evolvingCylinderModelJet_mem_sphereRegion ht.1 (ht.2.trans_lt htheta))
  exact ⟨delta, hdelta, fun t ht J hnear => hmargin _ ⟨t, ht, rfl⟩ J hnear⟩




theorem exists_evolvingCylinder_whole_collar_tolerance {C theta : ℝ}
    (hC : 0 < C) (htheta : theta < 1) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ epsilon0 → ∀ t ∈ Icc (0 : ℝ) theta,
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon t B →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 ∈
          collarJetRegion C (e 0) (e 2) ∩
            sectionalJetLowerRegion (1 / 4) (e 0) (e 1) := by
  obtain ⟨dC, hdC, hcollar⟩ := exists_evolvingCylinder_close_collar hC htheta
  obtain ⟨dS, hdS, hsphere⟩ := exists_evolvingCylinder_sphere_tolerance htheta
  refine ⟨min dC (min (1 / 2) (dS / 810)),
    lt_min hdC (lt_min (by norm_num) (by positivity)), ?_⟩
  intro epsilon hepsilon hsmall t ht B hB z hz
  refine ⟨hcollar epsilon hepsilon (hsmall.trans (min_le_left _ _)) t ht B hB z hz, ?_⟩
  have hhalf := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith only [hhalf]
  apply hsphere t ht
  exact (evolving_roundCylinderClose_twoJet_error hepsilon ht.1 (ht.2.trans_lt htheta)
    hB horder z hz).trans (by linarith only [hdelta])




theorem exists_standard_whole_collar {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {C theta : ℝ}
    (hC : 0 < C) (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ center : StandardCapSpace,
      ∃ N : StandardCylinderPatch epsilon⁻¹ center,
      ∀ t ∈ Icc (0 : ℝ) theta, ∀ z : UnitTwoSphere,
        metricTwoJet ((S.flow.metric t).pullbackCoefficients
          (centeredStandardPatchChart N z 0)) 0 ∈
            collarJetRegion C (e 0) (e 2) ∩
              sectionalJetLowerRegion (1 / 4) (e 0) (e 1) := by
  obtain ⟨epsilon, hepsilon, hmargin⟩ :=
    exists_evolvingCylinder_whole_collar_tolerance hC htheta
  have htime : theta ∈ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact ⟨htheta0, htheta⟩
  obtain ⟨A⟩ := S.asymptotic theta htime epsilon hepsilon
  obtain ⟨center, hx⟩ := (ne_univ_iff_exists_notMem A.compact_set).mp A.compact.ne_univ
  obtain ⟨N, hN⟩ := A.patches center hx
  have hfamily : RoundCylinderFamilyClose epsilon (Icc (0 : ℝ) theta)
      (fun t => roundCylinderPullback (S.flow.metric t) N.coordinate) := by
    simpa only [StandardSpacetimeCylinderClose, zero_add, div_one, one_mul] using hN
  refine ⟨epsilon, hepsilon, center, N, ?_⟩
  intro t ht z
  have hclose : RoundCylinderClose epsilon t
      (roundCylinderPullback (S.flow.metric t) N.coordinate) := by
    obtain ⟨bound, hbound, hjets⟩ := hfamily.2
    exact ⟨hfamily.1 t ht, bound, hbound, hjets t ht⟩
  have hjet := hmargin epsilon hepsilon le_rfl t ht _ hclose (z, 0)
    ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
  let f := centeredStandardPatchChart N z 0
  have hsource : (0 : E) ∈ f.source := by
    rw [mem_centeredStandardPatchChart_source]
    simp only [map_zero, add_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
  have heq : (S.flow.metric t).pullbackCoefficients f =ᶠ[𝓝 (0 : E)]
      centeredCylinderMetric (roundCylinderPullback (S.flow.metric t) N.coordinate) z 0 :=
    eventually_of_mem (f.open_source.mem_nhds hsource) (fun p hp =>
      centeredStandardPatchChart_pullback N z 0 (S.flow.metric t) hp)
  have htwo : metricTwoJet ((S.flow.metric t).pullbackCoefficients f) 0 =
      metricTwoJet (centeredCylinderMetric
        (roundCylinderPullback (S.flow.metric t) N.coordinate) z 0) 0 := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact htwo ▸ hjet

end PoincareConjecture.M44

import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipModel
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RicciJetNorm
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_StandardSphereMargin
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "J2" => MetricTwoJet 3

noncomputable local instance tipCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tipCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tipTwoJetNorm : NormedAddCommGroup J2 := Prod.normedAddCommGroup

noncomputable local instance tipTwoJetSpace : NormedSpace ℝ J2 := Prod.normedSpace

theorem exists_source_tip_ricci_jet_tolerance
    {K : Set J2} (hK : IsCompact K) (hinv : ∀ J ∈ K, J.1.IsInvertible)
    {mu alpha : ℝ} (halpha : 0 < alpha)
    (hmargin : ∀ J ∈ K, ∀ v : E,
      alpha * ‖v‖ ^ 2 ≤ (M44.jetRicciBilinear J - mu • J.1) v v) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ K, ∀ J' : J2, ‖J' - J‖ ≤ delta →
      J'.1.IsInvertible ∧ ∀ v : E,
        mu * J'.1 v v ≤ M44.jetRicciBilinear J' v v := by
  let : FiniteDimensional ℝ (MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ J2 := by infer_instance
  let : ProperSpace J2 := FiniteDimensional.proper ℝ J2
  let U : Set J2 := {J | J.1.IsInvertible}
  let F : J2 → MetricCoefficient 3 := fun J => M44.jetRicciBilinear J - mu • J.1
  have hU : IsOpen U := isOpen_ricciFlowOperator_domain 3
  have hcont : ContinuousOn F U := by
    intro J hJ
    have hricci : ContinuousAt (@M44.jetRicciBilinear 3) J :=
      (M44.contDiffAt_jetRicciBilinear hJ).continuousAt
    have hmetric : ContinuousAt (fun L : J2 => mu • L.1) J :=
      (continuousAt_fst : ContinuousAt (fun L : J2 => L.1) J).const_smul mu
    exact (hricci.sub hmetric).continuousWithinAt
  obtain ⟨radius, hradius, hinside⟩ := hK.exists_cthickening_subset_open hU hinv
  have hcompact : IsCompact (Metric.cthickening radius K) := hK.cthickening
  have huniform := hcompact.uniformContinuousOn_of_continuous (hcont.mono hinside)
  obtain ⟨delta, hdelta, hclose⟩ :=
    Metric.uniformContinuousOn_iff_le.mp huniform (alpha / 2) (by positivity)
  refine ⟨min radius delta, lt_min hradius hdelta, ?_⟩
  intro J hJ J' hnear
  have hdist : dist J' J ≤ min radius delta := by simpa only [dist_eq_norm] using hnear
  have hJ' : J' ∈ Metric.cthickening radius K :=
    Metric.mem_cthickening_of_dist_le J' J radius K hJ (hdist.trans (min_le_left _ _))
  have hJK : J ∈ Metric.cthickening radius K :=
    Metric.mem_cthickening_of_dist_le J J radius K hJ (by simpa only [dist_self] using hradius.le)
  have hnorm : ‖F J' - F J‖ ≤ alpha / 2 := by
    simpa only [dist_eq_norm] using hclose J' hJ' J hJK (hdist.trans (min_le_right _ _))
  refine ⟨hinside hJ', ?_⟩
  intro v
  have herr : |(F J' - F J) v v| ≤ (alpha / 2) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖F J' - F J‖ * ‖v‖ * ‖v‖ := (F J' - F J).le_opNorm₂ v v
      _ ≤ (alpha / 2) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hlower := (abs_le.mp herr).1
  change -((alpha / 2) * ‖v‖ ^ 2) ≤ F J' v v - F J v v at hlower
  have hmodel : alpha * ‖v‖ ^ 2 ≤ F J v v := hmargin J hJ v
  have hpositive : 0 ≤ F J' v v := by
    nlinarith only [hlower, hmodel, mul_nonneg halpha.le (sq_nonneg ‖v‖)]
  change 0 ≤ M44.jetRicciBilinear J' v v - mu * J'.1 v v at hpositive
  exact sub_nonneg.mp hpositive

theorem exists_source_standard_tip_ricci_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta : ℝ} (htheta : theta < 1) :
    ∃ mu : ℝ, 0 < mu ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ s ∈ Icc (0 : ℝ) theta, ∀ J : J2,
        ‖J - metricTwoJet (P.standard_cap.flow.metric s).euclideanCoefficients 0‖ ≤ delta →
        J.1.IsInvertible ∧ ∀ v : E, mu * J.1 v v ≤ M44.jetRicciBilinear J v v := by
  obtain ⟨c, hc, hricci⟩ := exists_source_standard_tip_ricci_lower P
  have htime : theta < P.standard_cap.flow.base.lifetime := by
    simpa only [P.standard_cap.lifetime_one] using htheta
  obtain ⟨ell, hell, B, hbackground⟩ :=
    M44.exists_standard_family_ellipticity_jet_bound P.standard_cap.flow.base
      htime (isCompact_singleton (x := (0 : E))) 2
  let mu := c / 12
  let alpha := c * ell / 4
  let jet : ℝ × E → J2 := fun p =>
    metricTwoJet (P.standard_cap.flow.metric p.1).euclideanCoefficients p.2
  let K := jet '' (Icc (0 : ℝ) theta ×ˢ ({0} : Set E))
  have hsub : Icc (0 : ℝ) theta ⊆ Ico 0 P.standard_cap.flow.base.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt htime⟩
  have hcont : ContinuousOn jet (Icc (0 : ℝ) theta ×ˢ ({0} : Set E)) :=
    (M44.continuousOn_euclidean_twoJet
      (uniqueDiffOn_Ico 0 P.standard_cap.flow.base.lifetime)
      P.standard_cap.flow.base.flow).mono (prod_mono hsub (subset_univ _))
  have hcompact : IsCompact K :=
    (isCompact_Icc.prod isCompact_singleton).image_of_continuousOn hcont
  have hinv : ∀ J ∈ K, J.1.IsInvertible := by
    rintro _ ⟨p, _hp, rfl⟩
    exact (P.standard_cap.flow.metric p.1).inner_isInvertible p.2
  have hmargin : ∀ J ∈ K, ∀ v : E,
      alpha * ‖v‖ ^ 2 ≤ (M44.jetRicciBilinear J - mu • J.1) v v := by
    rintro _ ⟨⟨s, x⟩, hs, rfl⟩ v
    have hx : x = 0 := hs.2
    subst x
    have hr := hricci s (hsub hs.1) v
    have he := (hbackground s hs.1 0 (mem_singleton 0)).1 v
    change ell * ‖v‖ ^ 2 ≤ (P.standard_cap.flow.metric s).inner 0 v v at he
    change alpha * ‖v‖ ^ 2 ≤
      (M44.jetRicciBilinear (metricTwoJet
        (P.standard_cap.flow.metric s).euclideanCoefficients 0) -
          mu • (P.standard_cap.flow.metric s).euclideanCoefficients 0) v v
    rw [M44.jetRicciBilinear_metricTwoJet (P.standard_cap.flow.connection s)]
    change alpha * ‖v‖ ^ 2 ≤ (P.standard_cap.flow.connection s).ricci 0 v v -
      mu * (P.standard_cap.flow.metric s).inner 0 v v
    dsimp only [alpha, mu]
    nlinarith only [hr, mul_le_mul_of_nonneg_left he hc.le]
  obtain ⟨delta, hdelta, hbound⟩ := exists_source_tip_ricci_jet_tolerance
    hcompact hinv (show 0 < alpha by dsimp only [alpha]; positivity) hmargin
  refine ⟨mu, by dsimp only [mu]; positivity, delta, hdelta, ?_⟩
  intro s hs J hnear
  exact hbound (jet (s, 0)) (mem_image_of_mem jet ⟨hs, mem_singleton 0⟩) J hnear

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticReadout
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsBounds
import Mathlib.Topology.UniformSpace.HeineCantor









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => StandardCapSpace
local notation "J4" => Jet E (MetricCoefficient 3) 4

noncomputable local instance capToleranceCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capToleranceCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace



theorem exists_uniform_cap_analyticJet_tolerance {K : Set J4} (hK : IsCompact K)
    (hinv : K ⊆ M34.curvatureJetDomain 3 2) {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ K, ∀ J' : J4, ‖J' - J‖ ≤ delta →
      J' ∈ M34.curvatureJetDomain 3 2 ∧
      ‖M34.scalarAnalyticJet 3 J' - M34.scalarAnalyticJet 3 J‖ ≤ nu := by
  have hfd (j : ℕ) : FiniteDimensional ℝ (E [×j]→L[ℝ] MetricCoefficient 3) := by
    induction j with
    | zero =>
        exact FiniteDimensional.of_injective
          (continuousMultilinearCurryFin0 ℝ E (MetricCoefficient 3)).toLinearMap
          (continuousMultilinearCurryFin0 ℝ E (MetricCoefficient 3)).injective
    | succ j ih =>
        let := ih
        exact FiniteDimensional.of_injective
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E)
            (MetricCoefficient 3)).toLinearMap
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E)
            (MetricCoefficient 3)).injective
  let : ∀ j : Fin 5, FiniteDimensional ℝ (E [×(j : ℕ)]→L[ℝ] MetricCoefficient 3) :=
    fun j => hfd j
  let : ProperSpace J4 := FiniteDimensional.proper ℝ J4
  obtain ⟨radius, hradius, hinside⟩ := hK.exists_cthickening_subset_open
    (M34.isOpen_curvatureJetDomain 3 2) hinv
  have hcompact : IsCompact (Metric.cthickening radius K) := hK.cthickening
  have huniform := hcompact.uniformContinuousOn_of_continuous
    ((M34.continuousOn_scalarAnalyticJet 3).mono hinside)
  obtain ⟨delta, hdelta, hclose⟩ := Metric.uniformContinuousOn_iff_le.mp huniform nu hnu
  refine ⟨min radius delta, lt_min hradius hdelta, ?_⟩
  intro J hJ J' hnear
  have hdist : dist J' J ≤ min radius delta := by simpa only [dist_eq_norm] using hnear
  have hJ' : J' ∈ Metric.cthickening radius K :=
    Metric.mem_cthickening_of_dist_le J' J radius K hJ (hdist.trans (min_le_left _ _))
  have hJK : J ∈ Metric.cthickening radius K :=
    Metric.mem_cthickening_of_dist_le J J radius K hJ (by simpa only [dist_self] using hradius.le)
  refine ⟨hinside hJ', ?_⟩
  simpa only [dist_eq_norm] using hclose J' hJ' J hJK (hdist.trans (min_le_right _ _))



theorem exists_standardCap_analyticJet_tolerance {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {theta : ℝ} (htheta : theta < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc 0 theta, ∀ x ∈ K, ∀ J : J4,
      ‖J - spatialJet 4 (fun z : ℝ × E => (S.metric z.1).euclideanCoefficients z.2)
        (t, x)‖ ≤ delta →
      J ∈ M34.curvatureJetDomain 3 2 ∧
      ‖M34.scalarAnalyticJet 3 J -
        ((S.connection t).scalarCurvature x, scalarGradientNorm (S.metric t) (S.connection t) x,
          (S.connection t).laplacian (S.connection t).scalarCurvature x +
            2 * (S.connection t).ricciNormSq x)‖ ≤ nu := by
  let jet : ℝ × E → J4 :=
    spatialJet 4 (fun z : ℝ × E => (S.metric z.1).euclideanCoefficients z.2)
  have hsub : Icc (0 : ℝ) theta ×ˢ K ⊆ Ico 0 S.base.lifetime ×ˢ (univ : Set E) :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt htheta⟩, mem_univ _⟩
  have hcont : ContinuousOn jet (Icc 0 theta ×ˢ K) := by
    apply continuousOn_pi.mpr
    intro j
    exact (M44.continuousOn_standard_spatialJet S.base j).mono hsub
  have hcompact := (isCompact_Icc.prod hK).image_of_continuousOn hcont
  have hinv : jet '' (Icc 0 theta ×ˢ K) ⊆ M34.curvatureJetDomain 3 2 := by
    rintro _ ⟨p, _hp, rfl⟩
    exact M34.metric_spatialJet_mem_curvatureJetDomain (S.metric p.1) 2 p.2
  obtain ⟨delta, hdelta, hbound⟩ := exists_uniform_cap_analyticJet_tolerance hcompact hinv hnu
  refine ⟨delta, hdelta, ?_⟩
  intro t ht x hx J hnear
  have h := hbound (jet (t, x)) (mem_image_of_mem jet ⟨ht, hx⟩) J hnear
  have hread : M34.scalarAnalyticJet 3 (jet (t, x)) =
      ((S.connection t).scalarCurvature x, scalarGradientNorm (S.metric t) (S.connection t) x,
        (S.connection t).laplacian (S.connection t).scalarCurvature x +
          2 * (S.connection t).ricciNormSq x) := by
    change M34.scalarAnalyticJet 3 (spatialJet 4
      (fun z : ℝ × E => (S.metric t).euclideanCoefficients z.2) (0, x)) = _
    simpa only [scalarGradientNorm_eq_tangentNorm]
      using M34.scalarAnalyticJet_spatialJet (S.connection t) x
  rwa [hread] at h

end PoincareConjecture.M47

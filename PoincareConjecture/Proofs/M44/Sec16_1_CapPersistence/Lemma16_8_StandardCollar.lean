import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StandardPatchChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PhysicalCollar
import PoincareConjecture.Definitions.M34StandardCapExistence












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance standardCollarCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance standardCollarCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance standardCollarTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance standardCollarTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem continuousOn_pullback_twoJet_time
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (F : RicciFlow 3 M J)
    {U : Set E} (hU : IsOpen U) {f : E → M} (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {x : E} (hx : x ∈ U) :
    ContinuousOn (fun t => metricTwoJet ((F.metric t).pullbackCoefficients f) x) J := by
  let B : ℝ × E → MetricCoefficient 3 := fun z => (F.metric z.1).pullbackCoefficients f z.2
  let B1 : ℝ × E → E →L[ℝ] MetricCoefficient 3 :=
    fun z => fderiv ℝ (fun y => B (z.1, y)) z.2
  let B2 : ℝ × E → E →L[ℝ] E →L[ℝ] MetricCoefficient 3 :=
    fun z => fderiv ℝ (fun y => B1 (z.1, y)) z.2
  have h0 : ContDiffOn ℝ ∞ B (J ×ˢ U) := contDiffOn_pullbackCoefficients_within F hU hf
  have h1 : ContDiffOn ℝ ∞ B1 (J ×ˢ U) := contDiffOn_spatialFDeriv_within h0 hJ hU
  have h2 : ContDiffOn ℝ ∞ B2 (J ×ˢ U) := contDiffOn_spatialFDeriv_within h1 hJ hU
  have h : ContinuousOn (fun z => (B z, B1 z, B2 z)) (J ×ˢ U) :=
    h0.continuousOn.prodMk (h1.continuousOn.prodMk h2.continuousOn)
  change ContinuousOn (fun t => (B (t, x), B1 (t, x), B2 (t, x))) J
  exact h.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, hx⟩)




theorem exists_evolvingCylinder_close_collar {C theta : ℝ}
    (hC : 0 < C) (htheta : theta < 1) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ epsilon0 → ∀ t ∈ Icc (0 : ℝ) theta,
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon t B →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 ∈
          collarJetRegion C (e 0) (e 2) := by
  obtain ⟨delta, hdelta, hmargin⟩ := exists_evolvingCylinder_collar_tolerance hC htheta
  refine ⟨min (1 / 2) (delta / 810), lt_min (by norm_num) (by positivity), ?_⟩
  intro epsilon hepsilon hsmall t ht B hB z hz
  have hhalf := hsmall.trans (min_le_left _ _)
  have hdelta' := hsmall.trans (min_le_right _ _)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith only [hhalf]
  apply hmargin t ht
  exact (evolving_roundCylinderClose_twoJet_error hepsilon ht.1 (ht.2.trans_lt htheta)
    hB horder z hz).trans (by linarith only [hdelta'])





theorem exists_standard_collar_chart {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {C theta : ℝ}
    (hC : 0 < C) (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E StandardCapSpace ∞,
      0 ∈ f.source ∧
      IsCompact ((fun t => metricTwoJet ((S.flow.metric t).pullbackCoefficients f) 0) ''
        Icc (0 : ℝ) theta) ∧
      ∀ t ∈ Icc (0 : ℝ) theta,
        metricTwoJet ((S.flow.metric t).pullbackCoefficients f) 0 ∈
          collarJetRegion C (e 0) (e 2) := by
  obtain ⟨epsilon, hepsilon, hmargin⟩ := exists_evolvingCylinder_close_collar hC htheta
  have htime : theta ∈ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact ⟨htheta0, htheta⟩
  obtain ⟨A⟩ := S.asymptotic theta htime epsilon hepsilon
  obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem A.compact_set).mp A.compact.ne_univ
  obtain ⟨N, hN⟩ := A.patches x hx
  obtain ⟨z, _hz⟩ := N.center_sphere
  let f := centeredStandardPatchChart N z 0
  have hsource : (0 : E) ∈ f.source := by
    rw [mem_centeredStandardPatchChart_source]
    simp only [map_zero, add_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
  have hfamily : RoundCylinderFamilyClose epsilon (Icc (0 : ℝ) theta)
      (fun t => roundCylinderPullback (S.flow.metric t) N.coordinate) := by
    simpa only [StandardSpacetimeCylinderClose, zero_add, div_one, one_mul] using hN
  have hcontinuous := continuousOn_pullback_twoJet_time
    (uniqueDiffOn_Ico 0 S.flow.base.lifetime) S.flow.base.flow
    f.open_source f.contMDiffOn hsource
  have hsub : Icc (0 : ℝ) theta ⊆ Ico (0 : ℝ) S.flow.base.lifetime := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_lt htime.2⟩
  refine ⟨f, hsource, isCompact_Icc.image_of_continuousOn (hcontinuous.mono hsub), ?_⟩
  intro t ht
  have hclose : RoundCylinderClose epsilon t
      (roundCylinderPullback (S.flow.metric t) N.coordinate) := by
    obtain ⟨bound, hbound, hjets⟩ := hfamily.2
    exact ⟨hfamily.1 t ht, bound, hbound, hjets t ht⟩
  have hjet := hmargin epsilon hepsilon le_rfl t ht _ hclose (z, 0)
    ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
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




theorem exists_standard_collar_point {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {C theta : ℝ}
    (hC : 0 < C) (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ x : StandardCapSpace, ∀ t ∈ Icc (0 : ℝ) theta,
      ∃ p q : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (S.flow.metric t) x p q ∧
        (S.flow.connection t).sectionalCurvature x p q <
          C⁻¹ * (S.flow.connection t).scalarCurvature x := by
  obtain ⟨f, hsource, _hcompact, hmargin⟩ := exists_standard_collar_chart S hC htheta0 htheta
  refine ⟨f 0, ?_⟩
  intro t ht
  apply exists_collar_plane_of_pullback_twoJet (S.flow.metric t) (S.flow.connection t)
    f.open_source f.contMDiffOn _ hsource C (e 0) (e 2) (hmargin t ht)
  intro y hy
  exact ⟨(f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩

end PoincareConjecture.M44

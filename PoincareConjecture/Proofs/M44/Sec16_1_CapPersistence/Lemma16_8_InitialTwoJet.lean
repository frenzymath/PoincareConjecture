import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialJetConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialTwoJetCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialTwoJetCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_initial_twoJet_cutoff (g0 : StandardInitialMetric)
    {K : Set E} (hK : IsCompact K) {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
        (tip : S.carrier) (scale eta : ℝ) (Q : SurgeryCapClose g0 S g tip scale eta),
      eta ≤ delta → K ⊆ g0.metric.ball 0 eta⁻¹ ∧
        ∀ x ∈ K, ‖metricTwoJet Q.normalizedCoefficients x -
          metricTwoJet g0.metric.euclideanCoefficients x‖ ≤ accuracy := by
  classical
  obtain ⟨d, hd, hdomain⟩ := exists_initial_comparison_domain_threshold g0 hK 2
  choose C hC hbound using fun j : Fin 3 =>
    SurgeryCapClose.exists_normalized_coefficient_jet_bound.{u} g0 hK j.val
  let B := ∑ j : Fin 3, C j
  have hB : 0 < B := Finset.sum_pos (fun j _ => hC j) Finset.univ_nonempty
  refine ⟨min d (accuracy / B), lt_min hd (div_pos haccuracy hB), ?_⟩
  intro S g tip scale eta Q hsmall
  obtain ⟨horder, hsub⟩ := hdomain eta Q.eta_pos (hsmall.trans (min_le_left _ _))
  refine ⟨hsub, ?_⟩
  intro x hx
  apply norm_metricTwoJet_sub_le
  intro j hj
  let i : Fin 3 := ⟨j, by omega⟩
  have h := hbound i S g tip scale eta Q (hj.trans horder) hsub x hx
  have hQ := Q.contDiffOn_normalizedCoefficients.contDiffAt
    (Q.toPartialDiffeomorph.open_source.mem_nhds (hsub hx))
  have hg := g0.metric.contDiffAt_euclideanCoefficients x
  rw [iteratedFDeriv_sub_apply
    (hQ.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))] at h
  have hCB : C i ≤ B := Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_univ i)
  have hsmall' : B * eta ≤ accuracy := by
    have hh := (le_div_iff₀ hB).mp (hsmall.trans (min_le_right _ _))
    simpa only [mul_comm] using hh
  exact h.trans ((mul_le_mul_of_nonneg_right hCB Q.eta_pos.le).trans hsmall')

end PoincareConjecture.M44

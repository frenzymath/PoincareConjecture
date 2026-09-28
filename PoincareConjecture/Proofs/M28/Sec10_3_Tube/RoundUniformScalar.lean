import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundGaussJetReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelCenterMetricJet
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundNormalizedGaussChart
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundGaussScalarReadout











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds



theorem exists_round_scalar_accuracy {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (epsilon : ℝ) (N : SingularRoundComponent g epsilon),
        epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier,
          |D.scalarCurvature x / N.scale - 6| < delta := by
  obtain ⟨eta, heta, hmodulus⟩ := exists_roundJet_scalar_uniform_modulus 0 4 hdelta
  let C : ℝ := 1 + ‖modelTensorConnectionLiftMap‖ * 2
  have hC : 0 < C := by dsimp [C]; positivity
  let epsilon₀ := min (1 / 200 : ℝ) (eta / (2 * C))
  have hepsilon₀ : 0 < epsilon₀ := by
    apply lt_min (by norm_num)
    exact div_pos heta (mul_pos (by norm_num) hC)
  refine ⟨epsilon₀, hepsilon₀, min_le_left _ _, ?_⟩
  intro M _ _ _ _ g D epsilon N hepsilon x hx
  have hsmall : C * epsilon < eta := by
    have h := hepsilon.trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp h
    nlinarith
  have hhalf : epsilon ≤ (1 / 2 : ℝ) :=
    (hepsilon.trans (min_le_left _ _)).trans (by norm_num)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    norm_num
    linarith
  obtain ⟨R, hR, e, he0, he, hi, hcenter, hgauss⟩ :=
    exists_normalized_gauss_parametrization N.model_metric (N.inverse x)
  have hmodel : metricTwoJet (N.model_metric.pullbackCoefficients e) 0 ∈
      roundJetScalarSixSet 0 4 := by
    exact ⟨round_model_center_metricTwoJet_mem_boundSet N hR e he hi hcenter hgauss,
      round_gauss_model_scalar_eq_six N isOpen_ball he hi (mem_ball_self hR)⟩
  have hdist := (round_gauss_two_jet_dist_le N hR e he hi hcenter hgauss horder).trans_lt
    hsmall
  have hscalar := hmodulus _ hmodel _ hdist
  rw [round_gauss_source_scalar_eq N D isOpen_ball he hi (mem_ball_self hR),
    he0, N.right_inverse hx] at hscalar
  exact hscalar



theorem exists_round_scalar_ratio_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (epsilon : ℝ) (N : SingularRoundComponent g epsilon),
        epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier, ∀ y ∈ N.carrier,
          D.scalarCurvature x ≤ 2 * D.scalarCurvature y := by
  obtain ⟨epsilon₀, hpos, hsmall, hclose⟩ :=
    exists_round_scalar_accuracy.{u} (delta := 1 / 2) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D epsilon N hepsilon
  exact round_scalar_ratio_of_normalized_close N D
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (hclose M g D epsilon N hepsilon)

end PoincareConjecture.M28.tube

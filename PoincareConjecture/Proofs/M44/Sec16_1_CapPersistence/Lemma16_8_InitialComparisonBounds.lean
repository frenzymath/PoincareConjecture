import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialCurvatureBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialJetConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_InitialPhaseBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

noncomputable local instance comparisonCoefficientNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance comparisonCoefficientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem exists_initial_comparison_metric_bounds (g₀ : StandardInitialMetric)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ delta a Z : ℝ, 0 < delta ∧ 0 < a ∧ 1 ≤ Z ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
        (tip : S.carrier) (scale eta : ℝ) (Q : SurgeryCapClose g₀ S g tip scale eta),
      eta ≤ delta → K ⊆ g₀.metric.ball 0 eta⁻¹ ∧
        ∀ x ∈ K, (∀ v : E, a * ‖v‖ ^ 2 ≤ Q.normalizedCoefficients x v v) ∧
          ∀ j ≤ m, ‖iteratedFDeriv ℝ j Q.normalizedCoefficients x‖ ≤ Z := by
  classical
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g₀ hK m
  obtain ⟨a, ha, hlower⟩ := SurgeryCapClose.exists_normalized_uniform_lower_bound g₀ hK
  obtain ⟨B, hB, hmodel⟩ := M36.exists_compact_local_jet_bound hK
    (fun x _ => g₀.metric.contDiffAt_euclideanCoefficients x) m
  choose C hC herror using fun j : Fin (m + 1) =>
    SurgeryCapClose.exists_normalized_coefficient_jet_bound.{u} g₀ hK j.val
  let Z := B + ∑ j : Fin (m + 1), C j
  have hsum : 0 ≤ ∑ j : Fin (m + 1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨min delta (1 / 2), a, Z, lt_min hdelta (by norm_num), ha,
    hB.trans (le_add_of_nonneg_right hsum), ?_⟩
  intro S g tip scale eta Q hsmall
  obtain ⟨horder, hsub⟩ := hdomain eta Q.eta_pos (hsmall.trans (min_le_left _ _))
  have hhalf : eta ≤ 1 / 2 := hsmall.trans (min_le_right _ _)
  refine ⟨hsub, ?_⟩
  intro x hx
  refine ⟨hlower S g tip scale eta Q hhalf hsub x hx, ?_⟩
  intro j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hnorm := herror i S g tip scale eta Q (hj.trans horder) hsub x hx
  have hQ := Q.contDiffOn_normalizedCoefficients.contDiffAt
    (Q.toPartialDiffeomorph.open_source.mem_nhds (hsub hx))
  have hg := g₀.metric.contDiffAt_euclideanCoefficients x
  rw [iteratedFDeriv_sub_apply
    (hQ.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))] at hnorm
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Q.normalizedCoefficients x -
          iteratedFDeriv ℝ j g₀.metric.euclideanCoefficients x‖ +
        ‖iteratedFDeriv ℝ j g₀.metric.euclideanCoefficients x‖ := norm_le_norm_sub_add _ _
    _ ≤ C i * eta + B := add_le_add hnorm (hmodel j hj x hx)
    _ ≤ C i + B := add_le_add
      (mul_le_of_le_one_right (hC i).le (by linarith only [hhalf])) le_rfl
    _ ≤ Z := by
      have hi := Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_univ i)
      dsimp [Z]
      linarith only [hi]

theorem exists_initial_comparison_curvature_bounds (g₀ : StandardInitialMetric)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ delta C : ℝ, 0 < delta ∧ 1 ≤ C ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
        (tip : S.carrier) (scale eta : ℝ) (Q : SurgeryCapClose g₀ S g tip scale eta),
      eta ≤ delta → ∀ D : LeviCivitaData Q.normalizedMetric,
        ∀ x ∈ K, ∀ j ≤ m, D.curvatureDerivativeNorm j (Q.map x) ≤ C := by
  obtain ⟨delta, a, Z, hdelta, ha, _, hmetric⟩ :=
    exists_initial_comparison_metric_bounds.{u} g₀ hK (m + 2)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pullback_curvature_bound m ha Z
  refine ⟨delta, C, hdelta, hC, ?_⟩
  intro S g tip scale eta Q hsmall D x hx j hj
  obtain ⟨hsub, hmetric⟩ := hmetric S g tip scale eta Q hsmall
  have heq : Q.normalizedMetric.pullbackCoefficients Q.map = Q.normalizedCoefficients := by
    funext y
    ext v w
    rfl
  have hinv : ∀ y ∈ Q.toPartialDiffeomorph.source,
      (mfderiv (𝓡 3) (𝓡 3) Q.map y).IsInvertible := by
    intro y hy
    have hd := Q.toPartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy
    exact ⟨hd.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  apply hbound Q.normalizedMetric D Q.toPartialDiffeomorph.open_source Q.map_smooth
    hinv x (hsub hx) ?_ ?_ j hj
  · rw [heq]
    exact (hmetric x hx).1
  · rw [heq]
    exact (hmetric x hx).2

end PoincareConjecture.M44

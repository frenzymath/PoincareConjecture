import PoincareConjecture.Proofs.M47.CanonicalNeckCoefficientBounds
import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open M34 Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private theorem exists_old_normalized_coefficient_bound {epsilon : ℝ}
    (D : RoundCylinderTwoTensor) (hD : RoundCylinderClose epsilon 0 D) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, z)‖ ≤ L := by
  let m := Nat.floor epsilon⁻¹
  obtain ⟨A, _, herror⟩ := capPersistence_exists_coordinate_error_jet_bound m
  obtain ⟨G, _, hGram⟩ := capNeckNormalization_exists_modelGram_center_jet_bound 0 m
  let L0 := A * Real.sqrt (epsilon ^ 2 / (1 / 2 : ℝ) ^ (2 + m)) + G
  refine ⟨max 1 L0, le_max_left _ _, ?_⟩
  intro q z hz j hj a b
  have hcenter : (0, z) ∈ (chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hsD := (hD.1 q a b).contDiffAt
    (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have hsG : ContDiffAt ℝ ∞ (fun y => roundCylinderGram 0 (chartAt E₂ q) y a b) (0, z) :=
    (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
  have h := herror epsilon D hD le_rfl q z hz j hj a b
  rw [sphere_chart_center_zero, fun_iteratedFDeriv_sub_apply
    (hsD.of_le (by exact_mod_cast le_top)) (hsG.of_le (by exact_mod_cast le_top))] at h
  exact ((norm_le_norm_sub_add _ _).trans (add_le_add h (hGram q z j hj a b))).trans
    (le_max_right _ _)




theorem exists_cap_neck_normalization_tolerance {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : RoundCylinderTwoTensor) (hD : RoundCylinderClose epsilon 0 D) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 / 2 ∧
      ∀ B : RoundCylinderTwoTensor, RoundCylinderTensorSmoothOn epsilon B →
      (∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, z)‖ ≤ rho) →
      ∀ beta : ℝ, |beta - 1| ≤ sigma →
        RoundCylinderClose epsilon 0 (fun z v w => beta * B z v w) := by
  obtain ⟨eta, heta, hperturb⟩ := exists_same_epsilon_neck_perturbation_tolerance
    hepsilon D hD
  obtain ⟨L, hL, hLbound⟩ := exists_old_normalized_coefficient_bound D hD
  let K : Set RoundCylinderCoordinates := ({0} : Set E₂) ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  obtain ⟨A, hA, hAbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_singleton (x := (0 : ℝ)))
    (by rintro u rfl; norm_num : ({0} : Set ℝ) ⊆ Iio 1)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K) (Nat.floor epsilon⁻¹)
  let delta := eta / (A + 1)
  have hdelta : 0 < delta := div_pos heta (by positivity)
  have hsmall : A * delta ≤ eta := by
    have heq : (A + 1) * delta = eta := by dsimp only [delta]; field_simp
    nlinarith
  let rho := delta / 4
  let sigma := min (1 / 2 : ℝ) (delta / (4 * (L + 1)))
  have hrho : 0 < rho := div_pos hdelta (by norm_num)
  have hden : 0 < 4 * (L + 1) := by linarith
  have hsigma : 0 < sigma := lt_min (by norm_num) (div_pos hdelta hden)
  have hsigmaHalf : sigma ≤ 1 / 2 := min_le_left _ _
  have htotal : 2 * rho + sigma * L ≤ delta := by
    have h := (le_div_iff₀ hden).mp
      (min_le_right (1 / 2 : ℝ) (delta / (4 * (L + 1))))
    change sigma * (4 * (L + 1)) ≤ delta at h
    dsimp only [rho]
    nlinarith
  refine ⟨rho, hrho, sigma, hsigma, hsigmaHalf, ?_⟩
  intro B hB hjet beta hbeta
  have hbetaBound : |beta| ≤ 2 := by
    have h := abs_le.mp (hbeta.trans hsigmaHalf)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  let T : RoundCylinderTwoTensor := fun z v w => beta * B z v w
  have hT : RoundCylinderTensorSmoothOn epsilon T := hB.const_mul
  apply hperturb T hT
  intro z hz k hk a
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hAbound 0 (mem_singleton 0) z.1 T D epsilon hT hD.1 (0, z.2)
    ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter delta hdelta.le
    (fun j hj i l => ?_) k hk a
  · simpa only [sphere_chart_center_zero] using h.trans hsmall
  · have hnew := (hB z.1 i l).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds hcenter)
    have hold := (hD.1 z.1 i l).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds hcenter)
    have hw := norm_iteratedFDeriv_weighted_sub_le hnew hold beta 1 j
    simp only [one_mul] at hw
    apply hw.trans
    exact (add_le_add
      (mul_le_mul hbetaBound (hjet z.1 z.2 hz j hj i l) (norm_nonneg _) (by norm_num))
      (mul_le_mul hbeta (hLbound z.1 z.2 hz j hj i l) (norm_nonneg _) hsigma.le)).trans
      htotal

end PoincareConjecture.M47

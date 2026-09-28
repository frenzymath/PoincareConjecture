import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilinear" => E →L[ℝ] E →L[ℝ] ℝ

private theorem initialModelJet_affine (m : ℕ) (u : ℝ) :
    iteratedFDeriv ℝ m (evolvingCylinderModelField u) 0 =
      (1 - u) • iteratedFDeriv ℝ m cylinderModelField 0 +
        u • iteratedFDeriv ℝ m
          (fun _ : E => cylinderHeightCovector.smulRight cylinderHeightCovector) 0 := by
  have hmodel := cylinderModelField_contDiff.contDiffAt (x := (0 : E))
  have hconstant : ContDiffAt ℝ ∞
      (fun _ : E => cylinderHeightCovector.smulRight cylinderHeightCovector) 0 :=
    contDiffAt_const
  change iteratedFDeriv ℝ m (fun x => (1 - u) • cylinderModelField x +
    u • cylinderHeightCovector.smulRight cylinderHeightCovector) 0 = _
  rw [fun_iteratedFDeriv_add_apply
    ((hmodel.const_smul (1 - u)).of_le (by exact_mod_cast le_top))
    ((hconstant.const_smul u).of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' (hmodel.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' (hconstant.of_le (by exact_mod_cast le_top))]

theorem source_initial_model_jet_bounds (m : ℕ) :
    ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
      (∀ u ∈ Icc (-1 : ℝ) 0,
        ‖iteratedFDeriv ℝ m (evolvingCylinderModelField u) (0 : E)‖ ≤ Z) ∧
      ∀ u v : ℝ,
        ‖iteratedFDeriv ℝ m (evolvingCylinderModelField u) (0 : E) -
          iteratedFDeriv ℝ m (evolvingCylinderModelField v) (0 : E)‖ ≤ L * |u - v| := by
  let A := iteratedFDeriv ℝ m cylinderModelField (0 : E)
  let B := iteratedFDeriv ℝ m
    (fun _ : E => cylinderHeightCovector.smulRight cylinderHeightCovector) 0
  refine ⟨2 * ‖A‖ + ‖B‖, ‖A‖ + ‖B‖, by positivity, by positivity, ?_, ?_⟩
  · intro u hu
    rw [initialModelJet_affine]
    have hfactor : |1 - u| ≤ 2 := by rw [abs_le]; constructor <;> linarith only [hu.1, hu.2]
    have htime : |u| ≤ 1 := by rw [abs_le]; exact ⟨hu.1, hu.2.trans (by norm_num)⟩
    calc
      _ ≤ ‖(1 - u) • A‖ + ‖u • B‖ := norm_add_le _ _
      _ = |1 - u| * ‖A‖ + |u| * ‖B‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 * ‖A‖ + 1 * ‖B‖ := add_le_add
        (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _))
        (mul_le_mul_of_nonneg_right htime (norm_nonneg _))
      _ = _ := by rw [one_mul]
  · intro u v
    rw [initialModelJet_affine, initialModelJet_affine]
    have heq : (1 - u) • A + u • B - ((1 - v) • A + v • B) =
        (u - v) • (B - A) := by module
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |u - v| * (‖B‖ + ‖A‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
      _ = _ := by ring

theorem exists_source_initial_terminal_jet_bound (m : ℕ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ {epsilon u : ℝ}, 0 < epsilon → epsilon ≤ 1 / 2 →
      u ∈ Icc (-1 : ℝ) 0 → ∀ {B : RoundCylinderTwoTensor},
      RoundCylinderClose epsilon u B → m ≤ ⌊epsilon⁻¹⌋₊ →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ‖iteratedFDeriv ℝ m (centeredCylinderMetric B z.1 z.2) (0 : E)‖ ≤ Z := by
  obtain ⟨C, hC, herror⟩ := exists_evolvingCylinderError_jet_bound m
  obtain ⟨Z, _L, hZ, _hL, hmodel, _hmodulus⟩ := source_initial_model_jet_bounds m
  refine ⟨C + Z, by positivity, ?_⟩
  intro epsilon u hepsilon hsmall hu B hclose horder z hz
  have herr := herror hepsilon hu hclose horder z hz
  have hB := evolving_centeredCylinderMetric_contDiffAt hclose z hz
  have hM := (evolvingCylinderModelField_contDiff u).contDiffAt (x := (0 : E))
  rw [fun_iteratedFDeriv_sub_apply (hB.of_le (by exact_mod_cast le_top))
    (hM.of_le (by exact_mod_cast le_top))] at herr
  apply (norm_le_norm_sub_add _ _).trans
  exact add_le_add (herr.trans (by nlinarith only [hC, hsmall])) (hmodel u hu)

end PoincareConjecture.M47

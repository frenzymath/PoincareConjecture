import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizationJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceIntrinsicError










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)




theorem exists_capNeckNormalization_ordinary_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ eta : ℝ, 0 < eta ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ epsilon →
      ∀ (B : RoundCylinderTwoTensor), RoundCylinderTensorSmoothOn delta B →
      (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
        ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
              roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau) →
      ∀ beta : ℝ, |beta - 1| ≤ eta →
      RoundCylinderClose epsilon 0 (fun z v w => beta *
        roundCylinderShift (epsilon⁻¹ - delta⁻¹) B z v w) := by
  let m : ℕ := Nat.floor epsilon⁻¹
  obtain ⟨G, hG, hGram⟩ := capNeckNormalization_exists_modelGram_center_jet_bound 0 m
  obtain ⟨C, hC, hCylinder⟩ := capPersistence_exists_intrinsic_error_bound m
  let sigma : ℝ := epsilon / (2 * (C + 1))
  have hsigma : 0 < sigma := div_pos hepsilon (by positivity)
  have heq : 2 * (C + 1) * sigma = epsilon := by
    dsimp [sigma]
    field_simp [show C + 1 ≠ 0 by positivity]
  have hsquare : 4 * (C + 1) ^ 2 * sigma ^ 2 = epsilon ^ 2 := by
    calc
      _ = (2 * (C + 1) * sigma) ^ 2 := by ring
      _ = _ := by rw [heq]
  have hstrict : C * sigma ^ 2 < epsilon ^ 2 := by
    have hlarge : C < 4 * (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
    exact (mul_lt_mul_of_pos_right hlarge (sq_pos_of_pos hsigma)).trans_eq hsquare
  let tau : ℝ := sigma / 4
  let eta : ℝ := min 1 (sigma / (2 * (G + 1)))
  have htau : 0 < tau := div_pos hsigma (by norm_num)
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hsigma (by positivity))
  refine ⟨tau, htau, eta, heta, ?_⟩
  intro delta hdelta hde B hB hOld beta hbeta
  have hetaBound : eta * (2 * (G + 1)) ≤ sigma :=
    (le_div_iff₀ (by positivity : 0 < 2 * (G + 1))).mp (min_le_right _ _)
  have hbetaAbs : |beta| ≤ 2 := by
    have h := hbeta.trans (min_le_left _ _)
    rw [abs_le] at h ⊢
    constructor <;> linarith
  have herrorBound : |beta| * tau + |beta - 1| * G ≤ sigma := by
    have hfirst := mul_le_mul_of_nonneg_right hbetaAbs htau.le
    have hsecond := mul_le_mul_of_nonneg_right hbeta hG
    have htauEq : 4 * tau = sigma := by dsimp [tau]; ring
    nlinarith
  let D : RoundCylinderTwoTensor := fun z v w => beta *
    roundCylinderShift (epsilon⁻¹ - delta⁻¹) B z v w
  have hs : RoundCylinderTensorSmoothOn epsilon D :=
    (hB.shift_of_mapsTo (fun s hs => capNeckNormalization_shift_mem hdelta hde hs)).const_mul
  refine ⟨hs, C * sigma ^ 2, hstrict, ?_⟩
  intro z hz
  have hzold := capNeckNormalization_shift_mem hdelta hde hz
  have hzero : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have hsD (a b : Fin 3) : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient D (chartAt E₂ z.1) y a b) (0, z.2) :=
    (hs z.1 a b).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hz⟩)
  apply hCylinder D z.1 z.2 hsD sigma hsigma.le
  intro j hj a b
  have hsB : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ z.1) y a b)
      (0, z.2 + (epsilon⁻¹ - delta⁻¹)) :=
    (hB z.1 a b).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hzold⟩)
  exact (capNeckNormalization_error_jet_le B z.1 z.2 (epsilon⁻¹ - delta⁻¹)
    beta j a b hsB (hOld z.1 _ hzold j hj a b)
      (hGram z.1 z.2 j hj a b)).trans herrorBound




theorem exists_capNeckNormalization_tolerance {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ eta : ℝ, 0 < eta ∧
      ∀ (delta : ℝ), 0 < delta → delta < delta0 →
      ∀ (B : RoundCylinderTwoTensor), RoundCylinderClose delta 0 B →
      ∀ beta : ℝ, |beta - 1| ≤ eta →
      RoundCylinderClose epsilon 0 (fun z v w => beta *
        roundCylinderShift (epsilon⁻¹ - delta⁻¹) B z v w) := by
  obtain ⟨tau, htau, eta, heta, hclose⟩ :=
    exists_capNeckNormalization_ordinary_tolerance hepsilon
  obtain ⟨K, hK, hOld⟩ :=
    capNeckNormalization_exists_old_error_jet_bound (Nat.floor epsilon⁻¹)
  let delta0 : ℝ := min (epsilon / 4) (tau / (K + 1))
  have hdelta0 : 0 < delta0 := lt_min (div_pos hepsilon (by norm_num))
    (div_pos htau (by positivity))
  refine ⟨delta0, hdelta0, eta, heta, ?_⟩
  intro delta hdelta hsmall B hB beta hbeta
  have hde : delta ≤ epsilon := by
    have h := hsmall.trans_le (min_le_left _ _)
    linarith
  have hm := Nat.floor_mono (inv_anti₀ hdelta hde)
  have hbound : K * delta ≤ tau := by
    have h := (lt_div_iff₀ (by positivity : 0 < K + 1)).mp
      (hsmall.trans_le (min_le_right _ _))
    nlinarith
  exact hclose delta hdelta hde B hB.1
    (fun q s hs j hj a b => (hOld delta hdelta B hB hm q s hs j hj a b).trans hbound)
    beta hbeta

end PoincareConjecture.M34

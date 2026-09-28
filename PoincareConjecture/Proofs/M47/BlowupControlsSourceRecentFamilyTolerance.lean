import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference










set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open M34 Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates


theorem exists_source_recent_family_coefficient_tolerance
    {gamma : ℝ} (hgamma : 0 < gamma) (T : ℝ) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ u ∈ Icc (-T) 0,
      ∀ (B C : RoundCylinderTwoTensor),
      RoundCylinderTensorSmoothOn (3 * gamma) B →
      RoundCylinderTensorSmoothOn (3 * gamma) C →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ →
        roundCylinderJetErrorSquared u C (Nat.floor (3 * gamma)⁻¹) z ≤ 2 * gamma ^ 2) →
      (∀ q : UnitTwoSphere, ∀ r ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹,
        ∀ j ≤ Nat.floor (3 * gamma)⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
            roundCylinderTensorCoefficient C (chartAt E₂ q) y a b) (0, r)‖ ≤ kappa) →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ →
        roundCylinderJetErrorSquared u B (Nat.floor (3 * gamma)⁻¹) z ≤ 6 * gamma ^ 2 := by
  let m := Nat.floor (3 * gamma)⁻¹
  let K : Set V := ({0} : Set E₂) ×ˢ Icc (-(3 * gamma)⁻¹) (3 * gamma)⁻¹
  obtain ⟨A, hA, hbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_Icc : IsCompact (Icc (-T) 0))
    (fun _ hu => hu.2.trans_lt zero_lt_one)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K) m
  let W : ℝ := ∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let eta := min 1 (gamma ^ 2 / (W + 1))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos (sq_pos_of_pos hgamma) (by positivity))
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hproduct : (W + 1) * eta ≤ gamma ^ 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < W + 1)).mp
      (min_le_right (1 : ℝ) (gamma ^ 2 / (W + 1)))
    change eta * (W + 1) ≤ gamma ^ 2 at h
    simpa only [mul_comm] using h
  have herror : W * eta ^ 2 ≤ gamma ^ 2 := by
    have hetasq : eta ^ 2 ≤ eta := by nlinarith only [heta.le, heta1]
    calc
      _ ≤ W * eta := mul_le_mul_of_nonneg_left hetasq hW
      _ ≤ (W + 1) * eta := mul_le_mul_of_nonneg_right (by linarith) heta.le
      _ ≤ _ := hproduct
  let kappa := eta / (A + 1)
  have hkappa : 0 < kappa := div_pos heta (by positivity)
  have hsmall : A * kappa ≤ eta := by
    have hid : (A + 1) * kappa = eta := by dsimp only [kappa]; field_simp
    nlinarith only [hid, hkappa]
  refine ⟨kappa, hkappa, ?_⟩
  intro u hu B C hB hC hbase hcoeff z hz
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ
      Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have harray (k : ℕ) (hk : k ≤ m) (a : Fin (2 + k) → Fin 3) :
      |roundCylinderIteratedDerivative u (chartAt E₂ z.1) B k
          (chartAt E₂ z.1 z.1, z.2) a -
        roundCylinderIteratedDerivative u (chartAt E₂ z.1) C k
          (chartAt E₂ z.1 z.1, z.2) a| ≤ eta := by
    have h := hbound u hu z.1 B C (3 * gamma) hB hC (0, z.2)
      ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter kappa hkappa.le
      (hcoeff z.1 z.2 hz) k hk a
    simpa only [sphere_chart_center_zero] using h.trans hsmall
  have h := cylinder_jet_error_weighted_le hu.2 B C m z
    (theta := 1) zero_lt_one harray
  norm_num only [one_add_one_eq_two, inv_one] at h
  change roundCylinderJetErrorSquared u B m z ≤ _
  change roundCylinderJetErrorSquared u B m z ≤
    2 * roundCylinderJetErrorSquared u C m z + 2 * W * eta ^ 2 at h
  have hb := hbase z hz
  change roundCylinderJetErrorSquared u C m z ≤ 2 * gamma ^ 2 at hb
  nlinarith only [h, hb, herror]

end PoincareConjecture.M47

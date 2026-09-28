import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNormalizedJets
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNormalizedSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

open Proofs.M47 M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem exists_source_initial_own_scalar_family_tolerance
    {epsilon omegaMax C L : ℝ} (hepsilon : 0 < epsilon)
    (homegaMax : 0 < omegaMax) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∃ omega delta0 : ℝ, 0 < omega ∧ omega ≤ omegaMax ∧ omega ≤ 1 ∧
      0 < delta0 ∧ delta0 ≤ epsilon ∧ delta0 ≤ 1 / 200 ∧
      ∀ {delta k R c : ℝ}, 0 < delta → delta ≤ delta0 →
      |k - 1| ≤ (16 / 5 : ℝ) * delta →
      (∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹, r + c ∈ Ioo (-R) R) →
      ∀ B : ℝ → RoundCylinderTwoTensor,
      (∀ v ∈ Icc (-1 - omega) 0, ∀ (theta : UnitTwoSphere) (a b : Fin 3),
        ContDiffOn ℝ ∞
          (fun p : V => roundCylinderTensorCoefficient (B v) (chartAt E₂ theta) p a b)
          ((chartAt E₂ theta).target ×ˢ Ioo (-R) R)) →
      (∀ v ∈ Icc (-1 - omega) 0, ∀ (theta : UnitTwoSphere) (r : ℝ),
        r ∈ Ioo (-R) R → ∀ j ≤ ⌊epsilon⁻¹⌋₊,
          ‖iteratedFDeriv ℝ j (centeredCylinderMetric (B v) theta r) (0 : E) -
            iteratedFDeriv ℝ j (evolvingCylinderModelField v) (0 : E)‖ ≤
              C * delta + L * omega) →
      0 < k ∧ MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-1 - omega) 0) ∧
        RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0)
          (fun u z v w => k * neckAxialTensorPullback 1 c (B (u / k)) z v w) := by
  obtain ⟨Z, K, hZ, hK, henergy⟩ :=
    exists_source_initial_normalized_native_bound (Nat.floor epsilon⁻¹)
  let a := epsilon / (2 * (K + 1))
  have ha : 0 < a := div_pos hepsilon (by positivity)
  have haEq : 2 * (K + 1) * a = epsilon := by
    dsimp only [a]
    field_simp
  have hKa : K * a ^ 2 < epsilon ^ 2 := by
    have hcoef : K < 4 * (K + 1) ^ 2 := by nlinarith only [hK, sq_nonneg K]
    calc
      _ < 4 * (K + 1) ^ 2 * a ^ 2 := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos ha)
      _ = _ := by rw [← haEq]; ring
  let M := 2 * C + (16 / 5 : ℝ) * Z
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let omega := min omegaMax (min 1 (a / (8 * (L + 1))))
  have homega : 0 < omega := lt_min homegaMax (lt_min zero_lt_one (by positivity))
  have homegaMax' : omega ≤ omegaMax := min_le_left _ _
  have homega1 : omega ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have homegaBound : omega ≤ a / (8 * (L + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let delta0 := min epsilon (min (1 / 200) (min (5 * omega / 32) (a / (4 * (M + 1)))))
  have hdelta0 : 0 < delta0 := by
    apply lt_min hepsilon
    apply lt_min (by norm_num)
    exact lt_min (by positivity) (by positivity)
  have hdeltaE : delta0 ≤ epsilon := min_le_left _ _
  have hdeltaSmall : delta0 ≤ 1 / 200 := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaOmega : delta0 ≤ 5 * omega / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaBound : delta0 ≤ a / (4 * (M + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLomega : 2 * L * omega ≤ a / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (L + 1))).mp homegaBound
    nlinarith only [h, homega.le]
  have hMdelta : M * delta0 ≤ a / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp hdeltaBound
    nlinarith only [h, hdelta0.le]
  let W := 2 * (C * delta0 + L * omega) + Z * ((16 / 5 : ℝ) * delta0)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hWa : W ≤ a := by
    have heq : W = M * delta0 + 2 * L * omega := by dsimp only [W, M]; ring
    rw [heq]
    linarith only [hMdelta, hLomega, ha]
  have hstrict : K * W ^ 2 < epsilon ^ 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW hWa 2) hK).trans_lt hKa
  refine ⟨omega, delta0, homega, homegaMax', homega1, hdelta0, hdeltaE, hdeltaSmall, ?_⟩
  intro delta k R c hdelta hdeltaLe hk hband B hsmooth hjets
  have hsigmaOmega : (16 / 5 : ℝ) * delta ≤ omega / 2 := by
    linarith only [hdeltaLe, hdeltaOmega]
  have hsigmaSmall : (16 / 5 : ℝ) * delta ≤ 1 / 4 := by
    linarith only [hdeltaLe, hdeltaSmall]
  obtain ⟨hkBounds, hclock⟩ := source_initial_own_scalar_interval
    homega.le homega1 hsigmaOmega hsigmaSmall hk
  have hkPos : 0 < k := by linarith only [hkBounds.1]
  have hk2 : k ≤ 2 := by linarith only [hkBounds.2]
  refine ⟨hkPos, hclock, ?_, K * W ^ 2, hstrict, ?_⟩
  · intro u hu
    exact source_initial_translated_tensor_smooth k (B (u / k))
      (hsmooth _ (hclock hu)) hband
  · intro u hu z hz
    have hzOld := hband z.2 hz
    have hzero : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
      rw [roundCylinder_sphereChart_target]
      trivial
    have hB : ContDiffAt ℝ ∞ (centeredCylinderMetric (B (u / k)) z.1 (z.2 + c))
        (0 : E) := by
      apply centeredCylinderBilinear_contDiffAt
      intro i j
      exact (hsmooth _ (hclock hu) z.1 i j).contDiffAt
        (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hzOld⟩)
    have hA : 0 ≤ C * delta + L * omega := by positivity
    have hsigma : 0 ≤ (16 / 5 : ℝ) * delta := by positivity
    have hbound := henergy hkPos hk2 hu.2 c (B (u / k)) z.1 z.2 hB
      (C * delta + L * omega) ((16 / 5 : ℝ) * delta) hA hsigma hk
      (hjets _ (hclock hu) z.1 _ hzOld)
    have hsmall : 2 * (C * delta + L * omega) + Z * ((16 / 5 : ℝ) * delta) ≤ W := by
      dsimp only [W]
      gcongr
    have hnonneg : 0 ≤ 2 * (C * delta + L * omega) +
        Z * ((16 / 5 : ℝ) * delta) := by positivity
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hnonneg hsmall 2) hK)

end PoincareConjecture.M47

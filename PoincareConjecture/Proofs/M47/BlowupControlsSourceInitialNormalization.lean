import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCenteredJets
import PoincareConjecture.Proofs.M47.CanonicalNeckAxialPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

open Proofs.M47 M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem source_initial_centered_translation (k c : ℝ) (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (r : ℝ) :
    centeredCylinderMetric
        (fun z v w => k * neckAxialTensorPullback 1 c B z v w) theta r =
      fun p => k • centeredCylinderMetric B theta (r + c) p := by
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  simp only [centeredCylinderMetric, centeredCylinderBilinear_basis,
    smul_apply, smul_eq_mul, roundCylinderTensorCoefficient,
    neckAxialTensorPullback, neckAxialSpaceMap, neckAxialLinearMap,
    Prod.fst_add, Prod.snd_add]
  congr 2 <;> simp [add_assoc]

theorem source_initial_model_normalization {k : ℝ} (hk : k ≠ 0) (u : ℝ) :
    (fun p : E => k • evolvingCylinderModelField (u / k) p -
      evolvingCylinderModelField u p) =
        fun p => (k - 1) • cylinderModelField p := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [evolvingCylinderModelField, add_apply, sub_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

theorem source_initial_own_scalar_clock {q k : ℝ} (hq : 0 < q) (hk : 0 < k)
    (T u : ℝ) :
    0 < q * k ∧ T + (u / k) / q = T + u / (q * k) := by
  refine ⟨mul_pos hq hk, ?_⟩
  rw [div_div, mul_comm k q]

theorem source_initial_own_scalar_interval {k sigma omega : ℝ}
    (homega : 0 ≤ omega) (homegaSmall : omega ≤ 1)
    (hsigma : sigma ≤ omega / 2) (hsigmaSmall : sigma ≤ 1 / 4)
    (hk : |k - 1| ≤ sigma) :
    k ∈ Icc (3 / 4 : ℝ) (5 / 4) ∧
      MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-1 - omega) 0) := by
  have hkl := (abs_le.mp hk).1
  have hku := (abs_le.mp hk).2
  have hkBounds : k ∈ Icc (3 / 4 : ℝ) (5 / 4) := by
    constructor <;> linarith only [hkl, hku, hsigmaSmall]
  have hkPos : 0 < k := by linarith only [hkBounds.1]
  have hsigmaNonneg : 0 ≤ sigma := (abs_nonneg _).trans hk
  have hproduct : 1 ≤ (1 + omega) * k := by
    have h1 := mul_le_mul_of_nonneg_left hkl (by linarith only [homega] : 0 ≤ 1 + omega)
    have h2 := mul_le_mul_of_nonneg_left homegaSmall hsigmaNonneg
    nlinarith only [h1, h2, hsigma]
  refine ⟨hkBounds, ?_⟩
  intro u hu
  constructor
  · apply (le_div_iff₀ hkPos).mpr
    nlinarith only [hu.1, hproduct]
  · exact div_nonpos_of_nonpos_of_nonneg hu.2 hkPos.le

end PoincareConjecture.M47

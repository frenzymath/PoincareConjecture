import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open Proofs.M47 M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilinear" => E →L[ℝ] E →L[ℝ] ℝ

theorem source_initial_normalized_jet_identity {k : ℝ} (hk : k ≠ 0)
    (u c : ℝ) (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (r : ℝ)
    (hB : ContDiffAt ℝ ∞ (centeredCylinderMetric B theta (r + c)) (0 : E))
    (j : ℕ) :
    iteratedFDeriv ℝ j (centeredCylinderMetric
        (fun z v w => k * neckAxialTensorPullback 1 c B z v w) theta r) (0 : E) -
      iteratedFDeriv ℝ j (evolvingCylinderModelField u) (0 : E) =
        k • (iteratedFDeriv ℝ j (centeredCylinderMetric B theta (r + c)) (0 : E) -
          iteratedFDeriv ℝ j (evolvingCylinderModelField (u / k)) (0 : E)) +
        (k - 1) • iteratedFDeriv ℝ j cylinderModelField (0 : E) := by
  have hM := (evolvingCylinderModelField_contDiff (u / k)).contDiffAt (x := (0 : E))
  have hU := (evolvingCylinderModelField_contDiff u).contDiffAt (x := (0 : E))
  have hS := cylinderModelField_contDiff.contDiffAt (x := (0 : E))
  have hmodel := congrArg (fun f : E → Bilinear => iteratedFDeriv ℝ j f (0 : E))
    (source_initial_model_normalization hk u)
  rw [fun_iteratedFDeriv_sub_apply
      ((hM.const_smul k).of_le (by exact_mod_cast le_top))
      (hU.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' (hM.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' (hS.of_le (by exact_mod_cast le_top))] at hmodel
  rw [source_initial_centered_translation,
    iteratedFDeriv_const_smul_apply' (hB.of_le (by exact_mod_cast le_top)), ← hmodel]
  module

theorem exists_source_initial_normalized_native_bound (m : ℕ) :
    ∃ Z K : ℝ, 0 ≤ Z ∧ 0 ≤ K ∧
      ∀ {k : ℝ}, 0 < k → k ≤ 2 → ∀ {u : ℝ}, u ≤ 0 →
      ∀ (c : ℝ) (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (r : ℝ),
      ContDiffAt ℝ ∞ (centeredCylinderMetric B theta (r + c)) (0 : E) →
      ∀ A sigma : ℝ, 0 ≤ A → 0 ≤ sigma → |k - 1| ≤ sigma →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (centeredCylinderMetric B theta (r + c)) (0 : E) -
        iteratedFDeriv ℝ j (evolvingCylinderModelField (u / k)) (0 : E)‖ ≤ A) →
      roundCylinderJetErrorSquared u
        (fun z v w => k * neckAxialTensorPullback 1 c B z v w) m (theta, r) ≤
          K * (2 * A + Z * sigma) ^ 2 := by
  classical
  let Z : ℝ := ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDeriv ℝ j cylinderModelField (0 : E)‖
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZj (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j cylinderModelField (0 : E)‖ ≤ Z :=
    Finset.single_le_sum
      (fun j _ => norm_nonneg (iteratedFDeriv ℝ j cylinderModelField (0 : E)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  obtain ⟨K, hK, henergy⟩ := exists_source_initial_centered_native_bound m
  refine ⟨Z, K, hZ, hK, ?_⟩
  intro k hk hk2 u hu c B theta r hB A sigma hA hsigma hksigma hjets
  have hnew : ContDiffAt ℝ ∞ (centeredCylinderMetric
      (fun z v w => k * neckAxialTensorPullback 1 c B z v w) theta r) (0 : E) := by
    rw [source_initial_centered_translation]
    exact hB.const_smul k
  apply henergy hu _ theta r hnew (2 * A + Z * sigma)
    (add_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg hZ hsigma))
  intro j hj
  rw [source_initial_normalized_jet_identity hk.ne' u c B theta r hB j]
  calc
    _ ≤ ‖k • (iteratedFDeriv ℝ j (centeredCylinderMetric B theta (r + c)) (0 : E) -
          iteratedFDeriv ℝ j (evolvingCylinderModelField (u / k)) (0 : E))‖ +
        ‖(k - 1) • iteratedFDeriv ℝ j cylinderModelField (0 : E)‖ := norm_add_le _ _
    _ = k * ‖iteratedFDeriv ℝ j (centeredCylinderMetric B theta (r + c)) (0 : E) -
          iteratedFDeriv ℝ j (evolvingCylinderModelField (u / k)) (0 : E)‖ +
        |k - 1| * ‖iteratedFDeriv ℝ j cylinderModelField (0 : E)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hk]
    _ ≤ 2 * A + sigma * Z := add_le_add
      (mul_le_mul hk2 (hjets j hj) (norm_nonneg _) (by norm_num))
      (mul_le_mul hksigma (hZj j hj) (norm_nonneg _) hsigma)
    _ = _ := by ring

end PoincareConjecture.M47

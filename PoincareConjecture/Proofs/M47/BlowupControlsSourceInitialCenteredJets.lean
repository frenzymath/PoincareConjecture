import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNativeEnergy
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderField
import PoincareConjecture.Proofs.M34.Mathlib.LinearPrecomposeLocalJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates
local notation "Bilinear" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable def initialNativeEvaluation (a b : Fin 3) : Bilinear →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ a))

private theorem initialNative_coefficient (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (c : ℝ) (a b : Fin 3) (y : V) :
    roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b =
      initialNativeEvaluation a b (centeredCylinderMetric B theta c
        (cylinderEuclideanEquiv.symm (y - (0, c)))) := by
  simp only [initialNativeEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, centeredCylinderMetric,
    centeredCylinderBilinear_basis, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]

private theorem initialNative_error (u : ℝ) (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (c : ℝ) (a b : Fin 3) (y : V) :
    roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b -
        roundCylinderGram u (chartAt E₂ theta) y a b =
      initialNativeEvaluation a b
        (centeredCylinderMetric B theta c (cylinderEuclideanEquiv.symm (y - (0, c))) -
          evolvingCylinderModelField u (cylinderEuclideanEquiv.symm (y - (0, c)))) := by
  rw [map_sub, ← initialNative_coefficient,
    ← centeredCylinderBilinear_evolving_gram u theta c]
  simp only [initialNativeEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, centeredCylinderBilinear_basis,
    ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]

theorem source_initial_native_coefficients_contDiffAt
    (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (c : ℝ)
    (hB : ContDiffAt ℝ ∞ (centeredCylinderMetric B theta c) (0 : E))
    (a b : Fin 3) :
    ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b) (0, c) := by
  have hcoord : ContDiffAt ℝ ∞
      (fun y : V => cylinderEuclideanEquiv.symm (y - (0, c))) (0, c) :=
    cylinderEuclideanEquiv.symm.contDiff.contDiffAt.comp _
      (contDiffAt_id.sub contDiffAt_const)
  have hB' : ContDiffAt ℝ ∞ (centeredCylinderMetric B theta c)
      (cylinderEuclideanEquiv.symm ((0, c) - (0, c))) := by
    simpa only [sub_self, map_zero] using hB
  have hcomp : ContDiffAt ℝ ∞ (fun y : V =>
      centeredCylinderMetric B theta c (cylinderEuclideanEquiv.symm (y - (0, c))))
      (0, c) := hB'.comp (0, c) hcoord
  have h : ContDiffAt ℝ ∞ (fun y : V => initialNativeEvaluation a b
      (centeredCylinderMetric B theta c (cylinderEuclideanEquiv.symm (y - (0, c)))))
      (0, c) := (initialNativeEvaluation a b).contDiff.contDiffAt.comp (0, c) hcomp
  simpa only [← initialNative_coefficient] using h

theorem exists_source_initial_centered_coefficient_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ) (B : RoundCylinderTwoTensor)
      (theta : UnitTwoSphere) (c : ℝ),
      ContDiffAt ℝ ∞ (centeredCylinderMetric B theta c) (0 : E) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (centeredCylinderMetric B theta c) (0 : E) -
        iteratedFDeriv ℝ j (evolvingCylinderModelField u) (0 : E)‖ ≤ A) →
      ∀ j ≤ m, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b -
          roundCylinderGram u (chartAt E₂ theta) y a b) (0, c)‖ ≤ C * A := by
  classical
  let V0 : ℝ := ∑ ab : Fin 3 × Fin 3, ‖initialNativeEvaluation ab.1 ab.2‖
  let L : V →L[ℝ] E := cylinderEuclideanEquiv.symm.toContinuousLinearMap
  let H : ℝ := max 1 ‖L‖
  have hV0 : 0 ≤ V0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hH : 1 ≤ H := le_max_left _ _
  refine ⟨V0 * H ^ m, mul_nonneg hV0 (pow_nonneg (zero_le_one.trans hH) _), ?_⟩
  intro u B theta c hB A hA hjets j hj a b
  let F : E → Bilinear := fun p =>
    centeredCylinderMetric B theta c p - evolvingCylinderModelField u p
  have hF : ContDiffAt ℝ ∞ F (0 : E) :=
    hB.sub (evolvingCylinderModelField_contDiff u).contDiffAt
  have hFjet : ‖iteratedFDeriv ℝ j F (0 : E)‖ ≤ A := by
    dsimp only [F]
    rw [fun_iteratedFDeriv_sub_apply (hB.of_le (by exact_mod_cast le_top))
      ((evolvingCylinderModelField_contDiff u).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    exact hjets j hj
  let f : E → ℝ := (initialNativeEvaluation a b) ∘ F
  have hf : ContDiffAt ℝ ∞ f (0 : E) :=
    (initialNativeEvaluation a b).contDiff.contDiffAt.comp _ hF
  have heval : ‖initialNativeEvaluation a b‖ ≤ V0 :=
    Finset.single_le_sum
      (fun ab _ => norm_nonneg (initialNativeEvaluation ab.1 ab.2)) (Finset.mem_univ (a, b))
  have hfjet : ‖iteratedFDeriv ℝ j f (0 : E)‖ ≤ V0 * A := by
    apply ((initialNativeEvaluation a b).norm_iteratedFDeriv_comp_left
      hF (by exact_mod_cast le_top)).trans
    exact mul_le_mul heval hFjet (norm_nonneg _) hV0
  have hpower : ‖L‖ ^ j ≤ H ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hH hj)
  have hfL : ContDiffAt ℝ (j : ℕ∞ω) f (L (0 : V)) := by
    simpa only [map_zero] using hf.of_le (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  have hpre := L.norm_iteratedFDeriv_comp_right_of_contDiffAt (x := (0 : V)) hfL
  have heq : (fun y => roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b -
      roundCylinderGram u (chartAt E₂ theta) y a b) =
        fun y : V => (f ∘ L) (y - (0, c)) := by
    funext y
    exact initialNative_error u B theta c a b y
  rw [heq, iteratedFDeriv_comp_sub, sub_self]
  simp only [map_zero] at hpre
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (0 : E)‖ * ‖L‖ ^ j := hpre
    _ ≤ (V0 * A) * H ^ m :=
      mul_le_mul hfjet hpower (pow_nonneg (norm_nonneg _) _) (mul_nonneg hV0 hA)
    _ = (V0 * H ^ m) * A := by ring

theorem exists_source_initial_centered_native_bound (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : ℝ}, u ≤ 0 →
      ∀ (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (c : ℝ),
      ContDiffAt ℝ ∞ (centeredCylinderMetric B theta c) (0 : E) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (centeredCylinderMetric B theta c) (0 : E) -
        iteratedFDeriv ℝ j (evolvingCylinderModelField u) (0 : E)‖ ≤ A) →
      roundCylinderJetErrorSquared u B m (theta, c) ≤ K * A ^ 2 := by
  obtain ⟨C, hC, hcoeff⟩ := exists_source_initial_centered_coefficient_bound m
  obtain ⟨K, hK, henergy⟩ := exists_source_initial_native_coefficient_bound m
  refine ⟨K * C ^ 2, mul_nonneg hK (sq_nonneg _), ?_⟩
  intro u hu B theta c hB A hA hjets
  have hb := henergy hu B theta c
    (source_initial_native_coefficients_contDiffAt B theta c hB) (C * A)
    (mul_nonneg hC hA) (hcoeff u B theta c hB A hA hjets)
  exact hb.trans_eq (by ring)

end PoincareConjecture.M47

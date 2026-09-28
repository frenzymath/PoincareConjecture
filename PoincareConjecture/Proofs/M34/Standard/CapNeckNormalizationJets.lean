import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizationModel
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderOrdinaryJets
import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem capNeckNormalization_exists_old_error_jet_bound (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (delta : ℝ), 0 < delta →
      ∀ (B : RoundCylinderTwoTensor), RoundCylinderClose delta 0 B →
      m ≤ Nat.floor delta⁻¹ → ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-delta⁻¹) delta⁻¹ → ∀ j ≤ m, ∀ a b : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ K * delta := by
  obtain ⟨C, hC, hbound⟩ := capPersistence_exists_coordinate_error_jet_bound m
  refine ⟨C * (Real.sqrt ((1 / 2 : ℝ) ^ (2 + m)))⁻¹, by positivity, ?_⟩
  intro delta hdelta B hB hm q s hs j hj a b
  have heq : Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + m)) =
      delta * (Real.sqrt ((1 / 2 : ℝ) ^ (2 + m)))⁻¹ := by
    rw [Real.sqrt_div (sq_nonneg delta), Real.sqrt_sq hdelta.le, div_eq_mul_inv]
  have h := hbound delta B hB hm q s hs j hj a b
  rw [sphere_chart_center_zero, heq] at h
  exact h.trans_eq (by ring)

theorem capNeckNormalization_error_jet_le
    (B : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s c beta : ℝ)
    (j : ℕ) (a b : Fin 3) {A G : ℝ}
    (hB : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b) (0, s + c))
    (herror : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s + c)‖ ≤ A)
    (hmodel : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ G) :
    ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient
        (fun z v w => beta * roundCylinderShift c B z v w) (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤
      |beta| * A + |beta - 1| * G := by
  let E : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient B (chartAt E₂ q) (y + (0, c)) a b -
      roundCylinderGram 0 (chartAt E₂ q) (y + (0, c)) a b
  let H : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderGram 0 (chartAt E₂ q) y a b
  have hE : ContDiffAt ℝ ∞ E (0, s) := by
    have hf : ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b)
        ((0, s) + (0, c) : RoundCylinderCoordinates) := by
      simpa only [Prod.mk_add_mk, add_zero] using
        hB.sub (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
    exact hf.comp (0, s) (contDiffAt_id.add contDiffAt_const)
  have hH : ContDiffAt ℝ ∞ H (0, s) :=
    (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
  have hEj : ‖iteratedFDeriv ℝ j E (0, s)‖ ≤ A := by
    have he := iteratedFDeriv_comp_add_right (𝕜 := ℝ) j
      (f := fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderGram 0 (chartAt E₂ q) y a b)
      (x := (0, s)) (0, c)
    have hh := congrArg norm he
    simp only [Prod.mk_add_mk, add_zero] at hh
    exact hh.le.trans herror
  have hscaled (alpha : ℝ) (f : RoundCylinderCoordinates → ℝ)
      (hf : ContDiffAt ℝ ∞ f (0, s)) {D : ℝ}
      (hfbound : ‖iteratedFDeriv ℝ j f (0, s)‖ ≤ D) :
      ‖iteratedFDeriv ℝ j (fun y => alpha * f y) (0, s)‖ ≤ |alpha| * D := by
    let L : ℝ →L[ℝ] ℝ := alpha • ContinuousLinearMap.id ℝ ℝ
    have h := L.norm_iteratedFDeriv_comp_left hf (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
    have hn : ‖L‖ = |alpha| := by simp [L, norm_smul, Real.norm_eq_abs]
    have heq : L ∘ f = fun y => alpha * f y := by rfl
    rw [heq, hn] at h
    exact h.trans (mul_le_mul_of_nonneg_left hfbound (abs_nonneg _))
  have heq : (fun y => roundCylinderTensorCoefficient
      (fun z v w => beta * roundCylinderShift c B z v w) (chartAt E₂ q) y a b -
        roundCylinderGram 0 (chartAt E₂ q) y a b) =
      fun y => beta * E y - (1 - beta) * H y := by
    funext y
    change beta * roundCylinderTensorCoefficient (roundCylinderShift c B)
      (chartAt E₂ q) y a b - H y = _
    rw [roundCylinderTensorCoefficient_shift]
    dsimp only [E, H]
    rw [roundCylinderGram_add_axial]
    ring
  rw [heq]
  apply (norm_iteratedFDeriv_sub_le_of_contDiffAt j
    (contDiffAt_const.mul hE |>.of_le (by exact_mod_cast le_top))
    (contDiffAt_const.mul hH |>.of_le (by exact_mod_cast le_top))).trans
  have hsecond := hscaled (1 - beta) H hH hmodel
  rw [abs_sub_comm 1 beta] at hsecond
  exact add_le_add (hscaled beta E hE hEj) hsecond

end PoincareConjecture.M34

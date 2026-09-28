import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizationJets

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem capPersistence_normalized_tensor_error_jet_le
    (B D : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s lambda : ℝ)
    (j : ℕ) (a b : Fin 3) {A E : ℝ}
    (hB : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b) (0, s))
    (hD : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, s))
    (hdiff : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, s)‖ ≤ A)
    (hold : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient (fun z v w => lambda * D z v w)
        (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ E) :
    ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient (fun z v w => lambda * B z v w)
        (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤
      |lambda| * A + E := by
  let f := fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
    roundCylinderTensorCoefficient D (chartAt E₂ q) y a b
  let h := fun y => lambda * roundCylinderTensorCoefficient D (chartAt E₂ q) y a b -
    roundCylinderGram 0 (chartAt E₂ q) y a b
  let L : ℝ →L[ℝ] ℝ := lambda • ContinuousLinearMap.id ℝ ℝ
  have hf : ContDiffAt ℝ ∞ f (0, s) := hB.sub hD
  have hh : ContDiffAt ℝ ∞ h (0, s) :=
    (contDiffAt_const.mul hD).sub (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
  have hLf : ContDiffAt ℝ ∞ (L ∘ f) (0, s) := L.contDiff.contDiffAt.comp (0, s) hf
  have heq : (fun y => roundCylinderTensorCoefficient (fun z v w => lambda * B z v w)
      (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) =
        L ∘ f + h := by
    funext y
    change lambda * roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
      roundCylinderGram 0 (chartAt E₂ q) y a b =
        lambda * (roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) +
        (lambda * roundCylinderTensorCoefficient D (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b)
    ring
  rw [heq, iteratedFDeriv_add_apply
    (hLf.of_le (by exact_mod_cast le_top)) (hh.of_le (by exact_mod_cast le_top))]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hold
  have hnorm : ‖L‖ = |lambda| := by simp [L, norm_smul, Real.norm_eq_abs]
  have hb := L.norm_iteratedFDeriv_comp_left hf (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  rw [hnorm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))

end PoincareConjecture.M34

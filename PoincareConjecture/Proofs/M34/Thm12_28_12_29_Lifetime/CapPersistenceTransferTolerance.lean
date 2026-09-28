import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalization

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem capPersistence_exists_old_transfer_accuracy (epsilon tau : ℝ)
    (hepsilon : 0 < epsilon) (htau : 0 < tau) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ epsilon ∧
      ∀ delta : ℝ, 0 < delta → delta < delta0 →
      Nat.floor epsilon⁻¹ + 1 ≤ Nat.floor delta⁻¹ ∧
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose delta 0 B →
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
      ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
            roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau / 2 := by
  let m := Nat.floor epsilon⁻¹
  obtain ⟨K, hK, hbound⟩ := capNeckNormalization_exists_old_error_jet_bound m
  let delta0 := min epsilon (min ((m + 2 : ℕ) : ℝ)⁻¹ (tau / (2 * (K + 1))))
  have hdelta0 : 0 < delta0 := lt_min hepsilon (lt_min (by positivity)
    (div_pos htau (by positivity)))
  refine ⟨delta0, hdelta0, min_le_left _ _, ?_⟩
  intro delta hdelta hd
  have hsmall : delta < ((m + 2 : ℕ) : ℝ)⁻¹ :=
    hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcast : ((m + 1 : ℕ) : ℝ) ≤ delta⁻¹ := by
    have hi : ((m + 2 : ℕ) : ℝ) < delta⁻¹ :=
      by simpa only [inv_inv] using
        (inv_lt_inv₀ (by positivity : 0 < ((m + 2 : ℕ) : ℝ)⁻¹) hdelta).mpr hsmall
    have hstep : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (m + 1)
    exact hstep.trans hi.le
  have hm : m + 1 ≤ Nat.floor delta⁻¹ :=
    (Nat.le_floor_iff (inv_nonneg.mpr hdelta.le)).mpr hcast
  refine ⟨hm, ?_⟩
  intro B hB q s hs j hj a b
  have hdsmall : delta ≤ tau / (2 * (K + 1)) :=
    hd.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : delta * (2 * (K + 1)) ≤ tau :=
    (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp hdsmall
  exact (hbound delta hdelta B hB (Nat.le_trans (Nat.le_succ m) hm)
    q s hs j hj a b).trans (by nlinarith)

end PoincareConjecture.M34

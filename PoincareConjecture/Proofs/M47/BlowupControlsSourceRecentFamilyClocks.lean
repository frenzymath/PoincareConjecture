import PoincareConjecture.Proofs.M47.CanonicalNeckAxialPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem source_recent_clock_parameter {H s u : ℝ}
    (hH : 0 < H) (hs : 0 ≤ s) (hu : u ∈ Icc (-H * s) 0) :
    ∃ w ∈ Icc (0 : ℝ) 1, u = -H * s * (1 - w) ∧ s + u / H = s * w := by
  by_cases hs0 : s = 0
  · have hu0 : u = 0 := le_antisymm hu.2 (by simpa only [hs0, mul_zero] using hu.1)
    exact ⟨1, by norm_num, by simp [hs0, hu0], by simp [hs0, hu0]⟩
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let w := 1 + u / (H * s)
    have hprod : 0 < H * s := mul_pos hH hspos
    have hw0 : 0 ≤ w := by
      have h := (le_div_iff₀ hprod).mpr (show (-1 : ℝ) * (H * s) ≤ u by linarith only [hu.1])
      dsimp only [w]
      linarith only [h]
    have hw1 : w ≤ 1 := by
      have h := div_nonpos_of_nonpos_of_nonneg hu.2 hprod.le
      dsimp only [w]
      linarith only [h]
    refine ⟨w, ⟨hw0, hw1⟩, ?_, ?_⟩
    · dsimp only [w]
      field_simp [hH.ne', hs0]
      ring
    · dsimp only [w]
      field_simp [hH.ne', hs0]

theorem source_recent_clock_difference_le {H H0 s v d w : ℝ}
    (hH : 0 < H) (hHL : H ≤ H0 + 1) (hv : 0 ≤ v)
    (hs : |s - v| ≤ d) (hscale : |H - H0| ≤ d) (hw : w ∈ Icc (0 : ℝ) 1) :
    |(-H * s * (1 - w)) - (-H0 * v * (1 - w))| ≤ (H0 + 1 + v) * d := by
  have hprod : |H * s - H0 * v| ≤ (H0 + 1 + v) * d := by
    have heq : H * s - H0 * v = H * (s - v) + (H - H0) * v := by ring
    rw [heq]
    calc
      _ ≤ |H * (s - v)| + |(H - H0) * v| := abs_add_le _ _
      _ = H * |s - v| + |H - H0| * v := by
        rw [abs_mul, abs_mul, abs_of_pos hH, abs_of_nonneg hv]
      _ ≤ (H0 + 1) * d + d * v := add_le_add
        (mul_le_mul hHL hs (abs_nonneg _) (hH.le.trans hHL))
        (mul_le_mul_of_nonneg_right hscale hv)
      _ = _ := by ring
  have heq : (-H * s * (1 - w)) - (-H0 * v * (1 - w)) =
      -(H * s - H0 * v) * (1 - w) := by ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hw.2)]
  exact ((mul_le_mul_of_nonneg_left (show 1 - w ≤ 1 by linarith only [hw.1])
    (abs_nonneg (H * s - H0 * v))).trans_eq (mul_one _)).trans hprod

theorem source_recent_translation_coefficient (B : RoundCylinderTwoTensor)
    (c : ℝ) (q : UnitTwoSphere) (p : V) (a b : Fin 3) :
    roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c B) (chartAt E₂ q) p a b =
      roundCylinderTensorCoefficient B (chartAt E₂ q) (p + (0, c)) a b := by
  simp only [roundCylinderTensorCoefficient, neckAxialTensorPullback, neckAxialSpaceMap,
    neckAxialLinearMap, one_smul, ContinuousLinearMap.fst_prod_snd,
    ContinuousLinearMap.id_apply, Prod.fst_add, Prod.snd_add]
  congr 2
  · exact congrArg (chartAt E₂ q).symm (add_zero p.1).symm
  · ring
  · exact congrArg (fun y : E₂ => (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm y)
      (roundCylinderCoordinateBasis a).1) (add_zero p.1).symm
  · exact congrArg (fun y : E₂ => (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm y)
      (roundCylinderCoordinateBasis b).1) (add_zero p.1).symm

theorem source_recent_translation_coefficient_jet (B D : RoundCylinderTwoTensor)
    (c : ℝ) (q : UnitTwoSphere) (r : ℝ) (j : ℕ) (a b : Fin 3) :
    iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c B) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c D) (chartAt E₂ q) y a b)
      (0, r) =
      iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, r + c) := by
  simp only [source_recent_translation_coefficient]
  simpa only [Prod.mk_add_mk, zero_add] using iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun y : V => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) j (0, c) (0, r)

end PoincareConjecture.M47

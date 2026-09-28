import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedOperators












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => E × E

local instance m64WeightedSource_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedSource_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64WeightedSource_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedSource_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64WeightedSource_dualGroup : NormedAddCommGroup (P →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedSource_dualSpace : NormedSpace ℝ (P →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64WeightedSource_pairGroup : NormedAddCommGroup (P →L[ℝ] P →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedSource_pairSpace : NormedSpace ℝ (P →L[ℝ] P →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace





def m64WeightedPairMetricDerivative
    (w : Fin 2 → ℝ) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : P →L[ℝ] P →L[ℝ] E →L[ℝ] ℝ :=
  let T := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    D.flip
  w 0 • T.bilinearComp (ContinuousLinearMap.fst ℝ E E) (ContinuousLinearMap.fst ℝ E E) +
    w 1 • T.bilinearComp (ContinuousLinearMap.snd ℝ E E) (ContinuousLinearMap.snd ℝ E E)





theorem m64WeightedPairMetricDerivative_apply
    (w : Fin 2 → ℝ) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v z : P) (a : E) :
    m64WeightedPairMetricDerivative w D v z a =
      w 0 * D a v.1 z.1 + w 1 * D a v.2 z.2 := rfl





theorem m64Trilinear_mixed_norm_bound (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C : ℝ} (hD : ‖D‖ ≤ C) (a v z : E) : |D a v z| ≤ C * ‖a‖ * ‖v‖ * ‖z‖ := by
  calc
    _ ≤ ‖D a‖ * ‖v‖ * ‖z‖ := (D a).le_opNorm₂ v z
    _ ≤ (‖D‖ * ‖a‖) * ‖v‖ * ‖z‖ := by gcongr; exact D.le_opNorm a
    _ ≤ _ := by gcongr





theorem m64WeightedPairMetricDerivative_norm_le
    (w : Fin 2 → ℝ) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda : ℝ} (hD : ‖D‖ ≤ C) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) :
    ‖m64WeightedPairMetricDerivative w D‖ ≤ 2 * Lambda * C := by
  have hC : 0 ≤ C := (norm_nonneg D).trans hD
  have hL : 0 ≤ Lambda := (hw 0).1.trans (hw 0).2
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [Real.norm_eq_abs, m64WeightedPairMetricDerivative_apply]
  calc
    _ ≤ |w 0 * D a v.1 z.1| + |w 1 * D a v.2 z.2| := abs_add_le _ _
    _ ≤ Lambda * (C * ‖a‖ * ‖v.1‖ * ‖z.1‖) +
        Lambda * (C * ‖a‖ * ‖v.2‖ * ‖z.2‖) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw 0).1]
        exact mul_le_mul (hw 0).2 (m64Trilinear_mixed_norm_bound D hD _ _ _)
          (abs_nonneg _) hL
      · rw [abs_mul, abs_of_nonneg (hw 1).1]
        exact mul_le_mul (hw 1).2 (m64Trilinear_mixed_norm_bound D hD _ _ _)
          (abs_nonneg _) hL
    _ ≤ Lambda * (C * ‖a‖ * ‖v‖ * ‖z‖) + Lambda * (C * ‖a‖ * ‖v‖ * ‖z‖) := by
      gcongr
      · exact norm_fst_le _
      · exact norm_fst_le _
      · exact norm_snd_le _
      · exact norm_snd_le _
    _ = _ := by ring




theorem m64WeightedPairMetricDerivative_sub
    (w : Fin 2 → ℝ) (D T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    m64WeightedPairMetricDerivative w (D - T) =
      m64WeightedPairMetricDerivative w D - m64WeightedPairMetricDerivative w T := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro z
  apply ContinuousLinearMap.ext
  intro a
  simp only [sub_apply, m64WeightedPairMetricDerivative_apply]
  ring





def m64WeightedQuadraticSource
    (w : Fin 2 → ℝ) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v : P) : E →L[ℝ] ℝ :=
  (-1 / 2 : ℝ) • m64WeightedPairMetricDerivative w D v v




theorem m64WeightedQuadraticSource_gradient_bound
    (w : Fin 2 → ℝ) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda : ℝ} (hD : ‖D‖ ≤ C) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) (v z : P) :
    ‖m64WeightedQuadraticSource w D v - m64WeightedQuadraticSource w D z‖ ≤
      (Lambda * C) * (‖v‖ + ‖z‖) * ‖v - z‖ := by
  let T := m64WeightedPairMetricDerivative w D
  have hT : ‖T‖ ≤ 2 * Lambda * C := m64WeightedPairMetricDerivative_norm_le w D hD hw
  have hdiag : T v v - T z z = T (v - z) v + T z (v - z) := by
    simp only [map_sub, sub_apply]
    abel
  have hpair (a b : P) : ‖T a b‖ ≤ (2 * Lambda * C) * ‖a‖ * ‖b‖ :=
    (T.le_opNorm₂ a b).trans (by gcongr)
  have hbound : ‖T v v - T z z‖ ≤
      (2 * Lambda * C) * (‖v‖ + ‖z‖) * ‖v - z‖ := by
    rw [hdiag]
    exact (norm_add_le _ _).trans ((add_le_add (hpair (v - z) v) (hpair z (v - z))).trans_eq
      (by ring))
  change ‖(-1 / 2 : ℝ) • T v v - (-1 / 2 : ℝ) • T z z‖ ≤ _
  rw [← smul_sub (-1 / 2 : ℝ) (T v v) (T z z), norm_smul, Real.norm_eq_abs]
  norm_num only [abs_div, abs_neg, abs_one]
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
    (by ring)





theorem m64WeightedQuadraticSource_base_bound
    (w : Fin 2 → ℝ) (D T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda d : ℝ} (hD : ‖D - T‖ ≤ C * d)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) (v : P) :
    ‖m64WeightedQuadraticSource w D v - m64WeightedQuadraticSource w T v‖ ≤
      (Lambda * C) * d * ‖v‖ ^ 2 := by
  have hnorm := m64WeightedPairMetricDerivative_norm_le w (D - T) hD hw
  have hpair := (m64WeightedPairMetricDerivative w (D - T)).le_opNorm₂ v v
  have hbound : ‖m64WeightedPairMetricDerivative w D v v -
      m64WeightedPairMetricDerivative w T v v‖ ≤ (2 * Lambda * (C * d)) * ‖v‖ * ‖v‖ := by
    have he := hpair.trans (show ‖m64WeightedPairMetricDerivative w (D - T)‖ * ‖v‖ * ‖v‖ ≤
        (2 * Lambda * (C * d)) * ‖v‖ * ‖v‖ by gcongr)
    simpa only [m64WeightedPairMetricDerivative_sub, sub_apply] using he
  unfold m64WeightedQuadraticSource
  rw [← smul_sub (-1 / 2 : ℝ) (m64WeightedPairMetricDerivative w D v v)
    (m64WeightedPairMetricDerivative w T v v), norm_smul, Real.norm_eq_abs]
  norm_num only [abs_div, abs_neg, abs_one]
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
    (by ring)

end PoincareConjecture

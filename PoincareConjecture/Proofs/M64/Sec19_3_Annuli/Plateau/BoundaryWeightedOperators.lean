import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNaturalGrowthBounds











set_option autoImplicit false

noncomputable section

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64WeightedOperator_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedOperator_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64WeightedOperator_pairGroup :
    NormedAddCommGroup ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64WeightedOperator_pairSpace :
    NormedSpace ℝ ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace





def m64WeightedPairMetric (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ) :
    (E × E) →L[ℝ] (E × E) →L[ℝ] ℝ :=
  w 0 • G.bilinearComp (ContinuousLinearMap.fst ℝ E E) (ContinuousLinearMap.fst ℝ E E) +
    w 1 • G.bilinearComp (ContinuousLinearMap.snd ℝ E E) (ContinuousLinearMap.snd ℝ E E)




theorem m64WeightedPairMetric_apply (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (v z : E × E) :
    m64WeightedPairMetric w G v z = w 0 * G v.1 z.1 + w 1 * G v.2 z.2 := rfl





theorem m64WeightedPairMetric_norm_le (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda : ℝ} (hG : ‖G‖ ≤ C) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) :
    ‖m64WeightedPairMetric w G‖ ≤ 2 * Lambda * C := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hL : 0 ≤ Lambda := (hw 0).1.trans (hw 0).2
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v z
  rw [Real.norm_eq_abs, m64WeightedPairMetric_apply]
  calc
    _ ≤ |w 0 * G v.1 z.1| + |w 1 * G v.2 z.2| := abs_add_le _ _
    _ ≤ Lambda * (C * ‖v.1‖ * ‖z.1‖) + Lambda * (C * ‖v.2‖ * ‖z.2‖) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw 0).1]
        exact mul_le_mul (hw 0).2 (m64Bilinear_norm_bound G hG _ _)
          (abs_nonneg _) hL
      · rw [abs_mul, abs_of_nonneg (hw 1).1]
        exact mul_le_mul (hw 1).2 (m64Bilinear_norm_bound G hG _ _)
          (abs_nonneg _) hL
    _ ≤ Lambda * (C * ‖v‖ * ‖z‖) + Lambda * (C * ‖v‖ * ‖z‖) := by
      gcongr
      · exact norm_fst_le _
      · exact norm_fst_le _
      · exact norm_snd_le _
      · exact norm_snd_le _
    _ = _ := by ring





theorem m64WeightedPairMetric_coercive (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ)
    {kappa mu : ℝ} (hk : 0 ≤ kappa) (hmu : 0 ≤ mu)
    (hG : ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G v v) (hw : ∀ i, mu ≤ w i) (v : E × E) :
    kappa * mu * ‖v‖ ^ 2 ≤ m64WeightedPairMetric w G v v := by
  have hdiag (i : Fin 2) (z : E) : kappa * mu * ‖z‖ ^ 2 ≤ w i * G z z := by
    calc
      _ = mu * (kappa * ‖z‖ ^ 2) := by ring
      _ ≤ w i * (kappa * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hw i) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hG z) (hmu.trans (hw i))
  rw [m64WeightedPairMetric_apply, Prod.norm_def]
  rcases le_total ‖v.1‖ ‖v.2‖ with hv | hv
  · rw [max_eq_right hv]
    have h0 : 0 ≤ w 0 * G v.1 v.1 := le_trans (by positivity) (hdiag 0 v.1)
    linarith [hdiag 1 v.2]
  · rw [max_eq_left hv]
    have h1 : 0 ≤ w 1 * G v.2 v.2 := le_trans (by positivity) (hdiag 1 v.2)
    linarith [hdiag 0 v.1]





theorem m64WeightedPairMetric_sub (w : Fin 2 → ℝ) (G H : E →L[ℝ] E →L[ℝ] ℝ) :
    m64WeightedPairMetric w (G - H) = m64WeightedPairMetric w G - m64WeightedPairMetric w H := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro z
  simp only [sub_apply, m64WeightedPairMetric_apply]
  ring





theorem m64WeightedPairMetric_gradient_bound
    (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda : ℝ} (hG : ‖G‖ ≤ C) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) (v z : E × E) :
    ‖m64WeightedPairMetric w G v - m64WeightedPairMetric w G z‖ ≤
      (2 * Lambda * C) * ‖v - z‖ := by
  rw [← map_sub]
  exact (m64WeightedPairMetric w G).le_of_opNorm_le
    (m64WeightedPairMetric_norm_le w G hG hw) _





theorem m64WeightedPairMetric_base_bound
    (w : Fin 2 → ℝ) (G H : E →L[ℝ] E →L[ℝ] ℝ)
    {C Lambda d : ℝ} (hG : ‖G - H‖ ≤ C * d)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) (v : E × E) :
    ‖m64WeightedPairMetric w G v - m64WeightedPairMetric w H v‖ ≤
      (2 * Lambda * C) * d * ‖v‖ := by
  have hnorm := m64WeightedPairMetric_norm_le w (G - H) hG hw
  rw [m64WeightedPairMetric_sub] at hnorm
  have h := (m64WeightedPairMetric w G - m64WeightedPairMetric w H).le_of_opNorm_le hnorm v
  simpa only [sub_apply, mul_assoc] using h





theorem m64WeightedPairMetric_strong_monotone
    (w : Fin 2 → ℝ) (G : E →L[ℝ] E →L[ℝ] ℝ)
    {kappa mu : ℝ} (hk : 0 ≤ kappa) (hmu : 0 ≤ mu)
    (hG : ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G v v) (hw : ∀ i, mu ≤ w i) (v z : E × E) :
    kappa * mu * ‖v - z‖ ^ 2 ≤
      (m64WeightedPairMetric w G v - m64WeightedPairMetric w G z) (v - z) := by
  rw [← map_sub]
  exact m64WeightedPairMetric_coercive w G hk hmu hG hw (v - z)

end PoincareConjecture

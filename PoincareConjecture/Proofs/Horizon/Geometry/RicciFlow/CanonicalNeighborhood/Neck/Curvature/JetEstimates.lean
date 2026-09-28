import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12

open scoped BigOperators

namespace PoincareConjecture.EpsilonNeck

open SpacetimeBounds CoordinateExponential

private theorem abs_four_terms_le (a b c d : ℝ) :
    |a - b - c + d| ≤ |a| + |b| + |c| + |d| := by
  simpa only [Real.norm_eq_abs] using (norm_add_le (a - b - c) d).trans
    (add_le_add ((norm_sub_le (a - b) c).trans
      (add_le_add (norm_sub_le a b) le_rfl)) le_rfl)

private theorem norm_apply_three_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) (u v w : E) :
    ‖T u v w‖ ≤ ‖T‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  exact ((T u v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (T.le_opNorm₂ u v) (norm_nonneg _))

private theorem norm_apply_four_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w z : E) :
    ‖T u v w z‖ ≤ ‖T‖ * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  exact ((T u v w).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (norm_apply_three_le T u v w) (norm_nonneg _))

theorem norm_jetChristoffel_le {J : MetricTwoJet 3} {δ : ℝ}
    (hi : ‖J.1.inverse‖ ≤ 2) (hfirst : ‖J.2.1‖ ≤ δ)
    (u v : EuclideanSpace ℝ (Fin 3)) :
    ‖jetChristoffel J u v‖ ≤ 3 * δ * ‖u‖ * ‖v‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hfirst
  calc
    _ ≤ ‖J.1.inverse‖ * ‖metricKoszulCovector J.2.1 u v‖ := J.1.inverse.le_opNorm _
    _ ≤ 2 * ((3 / 2 : ℝ) * δ * ‖u‖ * ‖v‖) := by
      apply mul_le_mul hi _ (norm_nonneg _) (by norm_num)
      exact (norm_metricKoszulCovector_le _ u v).trans (by gcongr)
    _ = _ := by ring

theorem jetCurvature_le_of_first_zero {J : MetricTwoJet 3} {K : ℝ}
    (hfirst : J.2.1 = 0) (hsecond : ‖J.2.2‖ ≤ K)
    (u w v z : EuclideanSpace ℝ (Fin 3))
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |jetCurvature J u w v z| ≤ 2 * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hsecond
  have hΓ (a b : EuclideanSpace ℝ (Fin 3)) : jetChristoffel J a b = 0 := by
    simp [jetChristoffel, hfirst, metricKoszulCovector]
  have hb (a b c d : EuclideanSpace ℝ (Fin 3))
      (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
      |J.2.2 a b c d| ≤ K := by
    calc
      _ ≤ ‖J.2.2‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := norm_apply_four_le _ _ _ _ _
      _ ≤ K * 1 * 1 * 1 * 1 := by gcongr
      _ = _ := by ring
  simp only [jetCurvature, hΓ, hfirst, zero_apply, map_zero,
    add_zero, sub_zero, neg_zero, abs_mul]
  have h := abs_four_terms_le (J.2.2 u z w v) (J.2.2 u v w z)
    (J.2.2 w z u v) (J.2.2 w v u z)
  have h₁ := hb u z w v hu hz hw hv
  have h₂ := hb u v w z hu hv hw hz
  have h₃ := hb w z u v hw hz hu hv
  have h₄ := hb w v u z hw hv hu hz
  norm_num
  linarith

theorem jetCurvature_sub_le {J J₀ : MetricTwoJet 3} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ‖J.1‖ ≤ 3) (hi : ‖J.1.inverse‖ ≤ 2)
    (hfirst : ‖J.2.1‖ ≤ δ) (hfirst₀ : J₀.2.1 = 0)
    (hsecond : ‖J.2.2 - J₀.2.2‖ ≤ δ)
    (u w v z : EuclideanSpace ℝ (Fin 3))
    (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |jetCurvature J u w v z - jetCurvature J₀ u w v z| ≤ 62 * δ := by
  have hΓ := norm_jetChristoffel_le hi hfirst
  have hΓ₀ (a b : EuclideanSpace ℝ (Fin 3)) : jetChristoffel J₀ a b = 0 := by
    simp [jetChristoffel, hfirst₀, metricKoszulCovector]
  have htwo (a b c d : EuclideanSpace ℝ (Fin 3))
      (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
      |J.2.2 a b c d - J₀.2.2 a b c d| ≤ δ := by
    have h := norm_apply_four_le (J.2.2 - J₀.2.2) a b c d
    simp only [sub_apply, Real.norm_eq_abs] at h
    calc
      _ ≤ ‖J.2.2 - J₀.2.2‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := h
      _ ≤ δ * 1 * 1 * 1 * 1 := by gcongr
      _ = δ := by ring
  have hfirstterm (a b c d : EuclideanSpace ℝ (Fin 3))
      (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
      |J.2.1 a (jetChristoffel J b c) d| ≤ 3 * δ ^ 2 := by
    calc
      _ ≤ ‖J.2.1‖ * ‖a‖ * ‖jetChristoffel J b c‖ * ‖d‖ :=
        norm_apply_three_le _ _ _ _
      _ ≤ δ * 1 * (3 * δ * 1 * 1) * 1 := by
        gcongr
        exact (hΓ b c).trans (by gcongr)
      _ = _ := by ring
  have hquad (a b c d : EuclideanSpace ℝ (Fin 3))
      (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
      |J.1 (jetChristoffel J a (jetChristoffel J b c)) d| ≤ 27 * δ ^ 2 := by
    calc
      _ ≤ ‖J.1‖ * ‖jetChristoffel J a (jetChristoffel J b c)‖ * ‖d‖ :=
        J.1.le_opNorm₂ _ _
      _ ≤ 3 * (3 * δ * 1 * (3 * δ * 1 * 1)) * 1 := by
        gcongr
        exact (hΓ a (jetChristoffel J b c)).trans (by
          gcongr
          exact (hΓ b c).trans (by gcongr))
      _ = _ := by ring
  have hlin : |(2⁻¹ : ℝ) *
      ((J.2.2 u z w v - J₀.2.2 u z w v) -
        (J.2.2 u v w z - J₀.2.2 u v w z) -
        (J.2.2 w z u v - J₀.2.2 w z u v) +
        (J.2.2 w v u z - J₀.2.2 w v u z))| ≤ 2 * δ := by
    rw [abs_mul]
    have h₁ := htwo u z w v hu hz hw hv
    have h₂ := htwo u v w z hu hv hw hz
    have h₃ := htwo w z u v hw hz hu hv
    have h₄ := htwo w v u z hw hv hu hz
    have ht := abs_four_terms_le
      (J.2.2 u z w v - J₀.2.2 u z w v) (J.2.2 u v w z - J₀.2.2 u v w z)
      (J.2.2 w z u v - J₀.2.2 w z u v) (J.2.2 w v u z - J₀.2.2 w v u z)
    norm_num
    linarith
  have hnonlin : |(-J.2.1 u (jetChristoffel J w z) v +
      J.2.1 w (jetChristoffel J u z) v +
      J.1 (jetChristoffel J u (jetChristoffel J w z)) v -
      J.1 (jetChristoffel J w (jetChristoffel J u z)) v)| ≤ 60 * δ ^ 2 := by
    calc
      _ ≤ |J.2.1 u (jetChristoffel J w z) v| +
          |J.2.1 w (jetChristoffel J u z) v| +
          |J.1 (jetChristoffel J u (jetChristoffel J w z)) v| +
          |J.1 (jetChristoffel J w (jetChristoffel J u z)) v| := by
        simpa only [Real.norm_eq_abs, abs_neg] using (norm_sub_le
          (-J.2.1 u (jetChristoffel J w z) v + J.2.1 w (jetChristoffel J u z) v +
            J.1 (jetChristoffel J u (jetChristoffel J w z)) v)
          (J.1 (jetChristoffel J w (jetChristoffel J u z)) v)).trans
          (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ 3 * δ ^ 2 + 3 * δ ^ 2 + 27 * δ ^ 2 + 27 * δ ^ 2 := by
        gcongr
        exact hfirstterm u w z v hu hw hz hv
        exact hfirstterm w u z v hw hu hz hv
        exact hquad u w z v hu hw hz hv
        exact hquad w u z v hw hu hz hv
      _ = _ := by ring
  have heq : jetCurvature J u w v z - jetCurvature J₀ u w v z =
      (2⁻¹ : ℝ) * ((J.2.2 u z w v - J₀.2.2 u z w v) -
        (J.2.2 u v w z - J₀.2.2 u v w z) -
        (J.2.2 w z u v - J₀.2.2 w z u v) +
        (J.2.2 w v u z - J₀.2.2 w v u z)) +
      (-J.2.1 u (jetChristoffel J w z) v + J.2.1 w (jetChristoffel J u z) v +
        J.1 (jetChristoffel J u (jetChristoffel J w z)) v -
        J.1 (jetChristoffel J w (jetChristoffel J u z)) v) := by
    simp only [jetCurvature, hΓ₀, hfirst₀, zero_apply,
      map_zero, add_zero, sub_zero, neg_zero]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hlin hnonlin).trans (by nlinarith))

end PoincareConjecture.EpsilonNeck

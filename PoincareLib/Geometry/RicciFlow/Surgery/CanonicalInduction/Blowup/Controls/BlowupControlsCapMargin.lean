import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry

/-!
# Fixed time margins in the cap comparison

The standard scalar lower rate becomes incompatible with a bounded
surviving line before normalized cap time one. These numerical constants
precede the flow; trajectory matching supplies the scalar input later.
Source: Morgan--Tian Claim 17.8, pp. 404-405.
-/

set_option autoImplicit false

namespace PoincareMT.M47

/-- Fixed interior comparison times with enough scalar-rate growth for
the bounded elapsed time and scalar ceiling in Claim 17.8. -/
theorem exists_cap_comparison_time_margin {c T D : ℝ}
    (hc : 0 < c) (hT : 0 ≤ T) (hD : 0 ≤ D) :
    ∃ theta1 theta2 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      0 < 2 * theta1 - 1 ∧ 2 * theta1 - 1 < theta1 ∧
      2 * T * D < c / (2 * (1 - (2 * theta1 - 1))) := by
  let eps := min (1 / 4 : ℝ) (c / (16 * (T * D + 1)))
  have hTD : 0 ≤ T * D := mul_nonneg hT hD
  have hden : 0 < 16 * (T * D + 1) := by positivity
  have heps : 0 < eps := lt_min (by norm_num) (div_pos hc hden)
  have hquarter : eps ≤ 1 / 4 := min_le_left _ _
  have hrate : eps * (16 * (T * D + 1)) ≤ c :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨1 - eps, (1 + (1 - eps)) / 2, by linarith, by linarith,
    by linarith, by linarith, by linarith, ?_⟩
  apply (lt_div_iff₀ (show 0 < 2 * (1 - (2 * (1 - eps) - 1)) by linarith)).mpr
  nlinarith [mul_nonneg heps.le hTD]

/-- The numerical contradiction in Claim 17.8 once the actual cap
comparison and surviving trajectory give the displayed scalar input. -/
theorem cap_elapsed_lt_time_margin {c T D H ell theta : ℝ}
    (hD : 0 ≤ D) (hH : 0 < H)
    (hell : ell ≤ T) (htheta : 1 / 2 < theta)
    (hrate : 2 * T * D < c / (2 * (1 - (2 * theta - 1))))
    (hcompare : theta * H ≤ ell →
      ∃ R : ℝ, R ≤ D ∧ c / (2 * (1 - (2 * theta - 1))) ≤ H * R) :
    ell < theta * H := by
  by_cases hhalf : ell ≤ H / 2
  · nlinarith
  · by_contra hnot
    obtain ⟨R, hR, hRateR⟩ := hcompare (le_of_not_gt hnot)
    have hHD : H * R ≤ H * D := mul_le_mul_of_nonneg_left hR hH.le
    have hHeight : H ≤ 2 * T := by linarith
    have hCeiling : H * D ≤ 2 * T * D := mul_le_mul_of_nonneg_right hHeight hD
    exact (not_le_of_gt hrate) (hRateR.trans (hHD.trans hCeiling))

end PoincareMT.M47

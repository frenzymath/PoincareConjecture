import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# The actual stereographic round-cylinder metric

For a positive angular scale b the global Euclidean coefficient matrix
is diag(b*rho,b*rho,1), where rho=16/(4+x0^2+x1^2)^2. These are the literal
centered unit-sphere stereographic coefficients. This is Morgan-Tian
Proposition 12.7, pp. 298-299 and cylinder-asymptotics-by-end-energy.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The everywhere-positive stereographic denominator
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderDenominator (x : E3) : ℝ := 4 + x 0 ^ 2 + x 1 ^ 2

/-- The literal unit-sphere conformal coefficient in centered charts
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderDensity (x : E3) : ℝ :=
  16 / stereographicCylinderDenominator x ^ 2

/-- The two angular coordinate directions as a continuous bilinear form
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderAngular : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0).smulRight (EuclideanSpace.proj 0) +
    (EuclideanSpace.proj 1).smulRight (EuclideanSpace.proj 1)

/-- The fixed axial coordinate direction as a continuous bilinear form
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderAxial : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
  (EuclideanSpace.proj 2).smulRight (EuclideanSpace.proj 2)

/-- Coefficients of the sphere of squared radius b times a fixed line
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderCoefficients (b : ℝ) (x : E3) :
    E3 →L[ℝ] E3 →L[ℝ] ℝ :=
  (b * stereographicCylinderDensity x) • stereographicCylinderAngular +
    stereographicCylinderAxial

/-- The exact scalar evaluation of the model coefficients
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCoefficients_apply (b : ℝ) (x u v : E3) :
    stereographicCylinderCoefficients b x u v =
      b * stereographicCylinderDensity x * (u 0 * v 0 + u 1 * v 1) + u 2 * v 2 := by
  simp only [stereographicCylinderCoefficients, stereographicCylinderAngular,
    stereographicCylinderAxial, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl

/-- The denominator is strictly positive on the whole Euclidean space
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderDenominator_pos (x : E3) :
    0 < stereographicCylinderDenominator x := by
  dsimp only [stereographicCylinderDenominator]
  positivity

/-- The literal sphere conformal coefficient is strictly positive
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderDensity_pos (x : E3) : 0 < stereographicCylinderDensity x :=
  div_pos (by norm_num) (sq_pos_of_pos (stereographicCylinderDenominator_pos x))

/-- The conformal coefficient is globally smooth
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderDensity_contDiff : ContDiff ℝ ∞ stereographicCylinderDensity := by
  have hd : ContDiff ℝ ∞ stereographicCylinderDenominator := by
    change ContDiff ℝ ∞ (fun x : E3 => 4 + EuclideanSpace.proj 0 x ^ 2 +
      EuclideanSpace.proj 1 x ^ 2)
    fun_prop
  exact contDiff_const.div (hd.pow 2) (fun x =>
    (sq_pos_of_pos (stereographicCylinderDenominator_pos x)).ne')

/-- The coefficient field is jointly smooth in scale and position,
without restricting the scale for this analytic assertion
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCoefficients_contDiff :
    ContDiff ℝ ∞ (fun z : ℝ × E3 => stereographicCylinderCoefficients z.1 z.2) := by
  have : IsBoundedSMul ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E3 →L[ℝ] E3 →L[ℝ] ℝ)
  exact (contDiff_fst.mul (stereographicCylinderDensity_contDiff.comp contDiff_snd)).smul
    contDiff_const |>.add contDiff_const

/-- Positive scale gives a positive-definite actual bilinear form
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCoefficients_pos {b : ℝ} (hb : 0 < b)
    (x u : E3) (hu : u ≠ 0) : 0 < stereographicCylinderCoefficients b x u u := by
  rw [stereographicCylinderCoefficients_apply]
  have hc : 0 < b * stereographicCylinderDensity x :=
    mul_pos hb (stereographicCylinderDensity_pos x)
  by_cases h0 : u 0 = 0
  · by_cases h1 : u 1 = 0
    · have h2 : u 2 ≠ 0 := by
        intro h2
        apply hu
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      simpa [h0, h1, ← sq] using sq_pos_of_ne_zero h2
    · have hp : 0 < u 0 * u 0 + u 1 * u 1 := by nlinarith [sq_pos_of_ne_zero h1]
      exact add_pos_of_pos_of_nonneg (mul_pos hc hp) (mul_self_nonneg _)
  · have hp : 0 < u 0 * u 0 + u 1 * u 1 := by nlinarith [sq_pos_of_ne_zero h0]
    exact add_pos_of_pos_of_nonneg (mul_pos hc hp) (mul_self_nonneg _)

/-- The genuine positive smooth Euclidean model metric at angular scale b
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderMetric (b : ℝ) (hb : 0 < b) : RiemannianMetric 3 E3 :=
  RiemannianMetric.ofEuclideanCoefficients (stereographicCylinderCoefficients b)
    (stereographicCylinderCoefficients_contDiff.comp (contDiff_const.prodMk contDiff_id))
    (fun x u v => by simp only [stereographicCylinderCoefficients_apply]; ring)
    (stereographicCylinderCoefficients_pos hb)

end PoincareMT.M34

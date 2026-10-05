import PoincareLib.Topology.Manifold.Surgery.Event.Stereographic.StereographicMetric
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean

/-!
# Curvature at the center of a sphere chart

The exact conformal metric coefficient determines every compatible
torsion-free connection by Koszul's formula. Its Christoffel symbol vanishes
at zero and its derivative gives the positive unit-curvature convention
retained by the project's curvature definition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M38

/-- The first derivative of the literal stereographic metric coefficient. -/
theorem hasFDerivAt_stereoWeight (z : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => 16 / (‖y‖ ^ 2 + 4) ^ 2)
      ((-64 / (‖z‖ ^ 2 + 4) ^ 3) • innerSL ℝ z) z := by
  have hd : ‖z‖ ^ 2 + 4 ≠ (0 : ℝ) := by positivity
  have hq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hi := (hasFDerivAt_inv (pow_ne_zero 2 hd)).comp z ((hq.add_const 4).pow 2)
  convert! hi.const_mul (16 : ℝ) using 1
  ext u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  <;> ring

/-- Differentiate an actual coordinate metric evaluation on fixed vectors. -/
theorem threeSphereStereoMetric_fderiv (a : UnitThreeSphere)
    (z u v w : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y => (threeSphereStereoMetric a).inner y v w) z u =
      (-64 / (‖z‖ ^ 2 + 4) ^ 3) * inner ℝ z u * inner ℝ v w := by
  simp_rw [threeSphereStereoMetric_inner]
  rw [((hasFDerivAt_stereoWeight z).mul_const (inner ℝ v w)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- Christoffel's bilinear expression for the actual stereographic metric. -/
noncomputable def stereoChristoffel (z u v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (-2 / (‖z‖ ^ 2 + 4)) •
    (inner ℝ u z • v + inner ℝ v z • u - inner ℝ u v • z)

/-- Koszul's identity determines these coefficients for any retained
Levi-Civita connection on this exact metric. -/
theorem threeSphereStereo_connection (a : UnitThreeSphere)
    (D : LeviCivitaData (threeSphereStereoMetric a))
    (z u v : EuclideanSpace ℝ (Fin 3)) :
    D.euclideanConnection u v z = stereoChristoffel z u v := by
  apply ext_inner_right ℝ
  intro w
  have hd : ‖z‖ ^ 2 + 4 ≠ (0 : ℝ) := by positivity
  have hc := D.inner_connection_const z u v w
  rw [threeSphereStereoMetric_inner, threeSphereStereoMetric_fderiv,
    threeSphereStereoMetric_fderiv, threeSphereStereoMetric_fderiv] at hc
  change 2 * (16 / (‖z‖ ^ 2 + 4) ^ 2 * inner ℝ (D.euclideanConnection u v z) w) = _
    at hc
  simp only [stereoChristoffel, inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm z u, real_inner_comm z v]
  rw [real_inner_comm u w] at hc
  field_simp at hc ⊢
  nlinarith

/-- The derivative of the Christoffel symbol at the chart center. -/
theorem hasFDerivAt_stereoChristoffel_zero (u v : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun z => stereoChristoffel z u v)
      ((-1 / 2 : ℝ) • ((innerSL ℝ u).smulRight v + (innerSL ℝ v).smulRight u -
        (inner ℝ u v) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))) 0 := by
  have hq := (hasStrictFDerivAt_norm_sq (0 : EuclideanSpace ℝ (Fin 3))).hasFDerivAt
  have hd : ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + 4 ≠ (0 : ℝ) := by norm_num
  have hi := ((hasFDerivAt_inv hd).comp 0 (hq.add_const 4)).const_mul (-2 : ℝ)
  have hlin := (((innerSL ℝ u).hasFDerivAt.smul_const v).add
    ((innerSL ℝ v).hasFDerivAt.smul_const u)).sub
      ((hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin 3))).const_smul (inner ℝ u v))
  convert! hi.smul hlin using 1
  ext w
  simp
  ring

/-- At zero the metric is Euclidean and the curvature has positive sign:
R(u,v)w = inner(v,w) u - inner(u,w) v. -/
theorem threeSphereStereo_curvature_zero (a : UnitThreeSphere)
    (D : LeviCivitaData (threeSphereStereoMetric a))
    (u v w : EuclideanSpace ℝ (Fin 3)) :
    D.curvature 0 u v w = inner ℝ v w • u - inner ℝ u w • v := by
  have he (b c : EuclideanSpace ℝ (Fin 3)) :
      D.euclideanConnection b c = fun z => stereoChristoffel z b c :=
    funext (fun z => threeSphereStereo_connection a D z b c)
  rw [D.curvature_eq_euclideanConnection]
  simp_rw [he]
  rw [(hasFDerivAt_stereoChristoffel_zero v w).fderiv,
    (hasFDerivAt_stereoChristoffel_zero u w).fderiv]
  change @Eq (EuclideanSpace ℝ (Fin 3)) _ _
  ext i
  simp only [stereoChristoffel, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_add, inner_zero_right, zero_smul, smul_zero, add_zero, sub_zero,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [real_inner_comm u v, real_inner_comm u w, real_inner_comm v w]
  ring

end PoincareMT.M38

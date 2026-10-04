import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.SphereCoordinates
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# Actual Euclidean metric for the literal cylinder chart

Morgan-Tian Definition 2.16, p. 30, used in Theorem 12.28, pp. 323-324.
The explicit preferred-chart Gram is realized as a genuine Riemannian
metric with M07's constructed Levi-Civita connection. This chart metric
is not asserted to be complete.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

/-- Definition 2.16, p. 30: the linear identification of Euclidean three-space
with the two sphere coordinates and the one axial coordinate. -/
noncomputable def cylinderCoordinateEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _)
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

/-- Definition 2.16, p. 30: the coordinate identification sends the first
two Euclidean components to the actual sphere-chart components. -/
theorem cylinderCoordinateEquiv_fst (p : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) :
    (cylinderCoordinateEquiv p).1 i = p (Fin.castAdd 1 i) := by
  rfl

/-- Definition 2.16, p. 30: the last Euclidean component is the axial coordinate. -/
theorem cylinderCoordinateEquiv_snd (p : EuclideanSpace ℝ (Fin 3)) :
    (cylinderCoordinateEquiv p).2 = p 2 := by
  rfl

/-- Definition 2.16, p. 30: the standard Euclidean basis is sent to the
literal basis used in the frozen cylinder coefficients. -/
theorem cylinderCoordinateEquiv_basis (i : Fin 3) :
    cylinderCoordinateEquiv (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      roundCylinderCoordinateBasis i := by
  apply Prod.ext
  · ext j
    rw [cylinderCoordinateEquiv_fst]
    fin_cases i <;> fin_cases j <;> simp [roundCylinderCoordinateBasis]
  · rw [cylinderCoordinateEquiv_snd]
    fin_cases i <;> simp [roundCylinderCoordinateBasis]

private noncomputable def spherePairing :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  let L := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  (innerSL ℝ : EuclideanSpace ℝ (Fin 2) →L[ℝ]
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).bilinearComp L L

private noncomputable def axialPairing :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  let A := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp A A

/-- Definition 2.16, p. 30: the actual stereographic cylinder metric
coefficients, transported by the displayed linear coordinate equivalence. -/
noncomputable def cylinderEuclideanCoefficients (u : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2) •
      spherePairing + axialPairing

/-- Definition 2.16, p. 30: evaluation of the genuine continuous bilinear
coefficient field gives precisely the literal model sphere and axial pairings. -/
theorem cylinderEuclideanCoefficients_apply (u : ℝ)
    (p v w : EuclideanSpace ℝ (Fin 3)) :
    cylinderEuclideanCoefficients u p v w =
      (32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2) *
        inner ℝ (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv w).1 +
        (cylinderCoordinateEquiv v).2 * (cylinderCoordinateEquiv w).2 := by
  rfl

private theorem cylinder_coefficients_smooth (u : ℝ) :
    ContDiff ℝ ∞ (cylinderEuclideanCoefficients u) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  have hn : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖(cylinderCoordinateEquiv p).1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_fst.comp cylinderCoordinateEquiv.contDiff)
  have hf : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 3) =>
      32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div ((hn.add contDiff_const).pow 2)
      (fun p => ne_of_gt (by positivity))
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight spherePairing
  exact (L.contDiff.comp hf).add contDiff_const

private theorem cylinder_coefficients_symm (u : ℝ)
    (p v w : EuclideanSpace ℝ (Fin 3)) :
    cylinderEuclideanCoefficients u p v w = cylinderEuclideanCoefficients u p w v := by
  rw [cylinderEuclideanCoefficients_apply, cylinderEuclideanCoefficients_apply,
    real_inner_comm (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv w).1,
    mul_comm (cylinderCoordinateEquiv v).2 (cylinderCoordinateEquiv w).2]

private theorem cylinder_coefficients_pos {u : ℝ} (hu : u < 1)
    (p v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    0 < cylinderEuclideanCoefficients u p v v := by
  have hf : 0 < 32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2 :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hu)) (by positivity)
  rw [cylinderEuclideanCoefficients_apply]
  by_cases hfirst : (cylinderCoordinateEquiv v).1 = 0
  · have hlast : (cylinderCoordinateEquiv v).2 ≠ 0 := by
      intro hlast
      apply hv
      apply cylinderCoordinateEquiv.injective
      rw [map_zero]
      exact Prod.ext hfirst hlast
    rw [hfirst, inner_zero_left, mul_zero, zero_add]
    exact mul_self_pos.mpr hlast
  · exact add_pos_of_pos_of_nonneg (mul_pos hf (real_inner_self_pos.mpr hfirst))
      (mul_self_nonneg _)

/-- Definition 2.16, p. 30: a genuine smooth Riemannian metric representing
the literal cylinder in Euclidean coordinates before its singular time. -/
noncomputable def cylinderEuclideanMetric (u : ℝ) (hu : u < 1) :
    RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients (cylinderEuclideanCoefficients u)
    (cylinder_coefficients_smooth u) (cylinder_coefficients_symm u)
    (cylinder_coefficients_pos hu)

/-- Definition 2.16, p. 30: the constructed smooth torsion-free metric
connection for the actual Euclidean cylinder chart metric. -/
noncomputable def cylinderEuclideanConnection (u : ℝ) (hu : u < 1) :
    LeviCivitaData (cylinderEuclideanMetric u hu) :=
  (cylinderEuclideanMetric u hu).euclideanLeviCivitaData

/-- Definition 2.16, p. 30: the actual Euclidean metric has exactly the
frozen model Gram coefficients, for every preferred sphere chart. -/
theorem cylinderEuclideanMetric_basis (u : ℝ) (hu : u < 1) (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) (a b : Fin 3) :
    (cylinderEuclideanMetric u hu).inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (cylinderCoordinateEquiv p) a b := by
  change cylinderEuclideanCoefficients u p
    (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) = _
  rw [cylinderEuclideanCoefficients_apply, cylinderCoordinateEquiv_basis,
    cylinderCoordinateEquiv_basis, roundCylinderGram_apply]

end PoincareMT.M35

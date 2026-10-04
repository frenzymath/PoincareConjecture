import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.SphereCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Jets.CylinderJetNorm

/-!
# Central connection coefficients of the literal cylinder

Morgan-Tian Definition 2.16, p. 30, and the analytic neck estimates in
Theorem 12.28, pp. 323-324. The first derivatives of the actual model Gram
vanish at the preferred center. The frozen connection therefore vanishes
there, identifying the first covariant metric-error jet with an ordinary jet.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

/-- Definition 2.16, p. 30: actual model metric derivatives at any coordinate
point, retaining the precise stereographic conformal factor. -/
theorem fderiv_roundCylinderGram_apply (u : ℝ) (q : UnitTwoSphere)
    (p v : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) p v =
      (-128 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 v.1 *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 := by
  have h := (((hasFDerivAt_stereographicMetricFactor (32 * (1 - u)) p.1).comp
    p hasFDerivAt_fst).mul_const
      (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1)).add_const
        ((roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2)
  simp_rw [roundCylinderGram_apply]
  convert! congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ => L v) h.fderiv using 1
  simp
  ring

/-- Definition 2.16, p. 30: all first coordinate derivatives of the actual
model metric vanish at the central sphere coordinate, at every axial point. -/
theorem hasFDerivAt_roundCylinderGram_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (a b : Fin 3) :
    HasFDerivAt (𝕜 := ℝ) (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
      0 (0, s) := by
  have hfactor : HasFDerivAt (𝕜 := ℝ) (fun p : RoundCylinderCoordinates =>
      32 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 2) 0 (0, s) := by
    have hf : HasFDerivAt (𝕜 := ℝ) (Prod.fst : RoundCylinderCoordinates →
        EuclideanSpace ℝ (Fin 2))
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) (0, s) :=
      hasFDerivAt_fst
    convert! (hasFDerivAt_stereographicMetricFactor (32 * (1 - u))
      (0 : EuclideanSpace ℝ (Fin 2))).comp ((0, s) : RoundCylinderCoordinates) hf using 1
    simp
  simp_rw [roundCylinderGram_eq]
  fin_cases a <;> fin_cases b <;> simp only [Matrix.diagonal] <;>
    first | exact hfactor | exact hasFDerivAt_const _ _

/-- Definition 2.16, p. 30: every model Christoffel coefficient is zero
at the center of the exact chart used by the frozen norm. -/
theorem roundCylinderChristoffel_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (0, s) a b d = 0 := by
  unfold roundCylinderChristoffel
  simp only [(hasFDerivAt_roundCylinderGram_center u q s _ _).fderiv]
  simp

/-- Definition 2.16, p. 30: the literal covariant derivative at the model
chart center is the ordinary directional derivative, for every tensor rank. -/
theorem roundCylinderTensorDerivative_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      T (0, s) a =
      fderiv ℝ (fun p => T p (fun i => a i.succ)) (0, s)
        (roundCylinderCoordinateBasis (a 0)) := by
  simp [roundCylinderTensorDerivative, roundCylinderChristoffel_center]

/-- Definition 2.16, p. 30: the first covariant metric-error jet is the
ordinary first metric jet at the preferred center. The model first jet is zero. -/
theorem roundCylinderIteratedDerivative_one_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (B : RoundCylinderTwoTensor) (a : Fin 3 → Fin 3)
    (hB : DifferentiableAt ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        p (a 1) (a 2)) (0, s)) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      B 1 (0, s) a =
      fderiv ℝ (fun p : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          p (a 1) (a 2)) (0, s) (roundCylinderCoordinateBasis (a 0)) := by
  rw [roundCylinderIteratedDerivative, roundCylinderTensorDerivative_center]
  change fderiv ℝ (fun p : RoundCylinderCoordinates =>
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      p (a 1) (a 2) -
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2))
    (0, s) _ = _
  have h := hB.hasFDerivAt.sub (hasFDerivAt_roundCylinderGram_center u q s (a 1) (a 2))
  have he := congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
    L (roundCylinderCoordinateBasis (a 0))) h.fderiv
  simp only [sub_zero] at he
  convert! he using 1

end PoincareMT.M35

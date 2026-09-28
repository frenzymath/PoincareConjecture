import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderReflection

noncomputable def coordinates : RoundCylinderCoordinates ≃L[ℝ] RoundCylinderCoordinates :=
  (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
    (ContinuousLinearEquiv.neg ℝ)

@[simp] theorem coordinates_apply (p : RoundCylinderCoordinates) :
    coordinates p = (p.1, -p.2) := rfl

@[simp] theorem coordinates_involutive (p : RoundCylinderCoordinates) :
    coordinates (coordinates p) = p := by simp

def space (z : RoundCylinderSpace) : RoundCylinderSpace := (z.1, -z.2)

@[simp] theorem space_involutive (z : RoundCylinderSpace) : space (space z) = z := by
  simp [space]

def sign (a : Fin 3) : ℝ := if a = 2 then -1 else 1

@[simp] theorem sign_mul_self (a : Fin 3) : sign a * sign a = 1 := by
  simp only [sign]
  split <;> norm_num

@[simp] theorem sign_sq (a : Fin 3) : sign a ^ 2 = 1 := by
  simpa only [pow_two] using sign_mul_self a

@[simp] theorem sign_inv (a : Fin 3) : (sign a)⁻¹ = sign a := by
  simp only [sign]
  split <;> norm_num

theorem coordinates_basis (a : Fin 3) :
    coordinates (roundCylinderCoordinateBasis a) = sign a • roundCylinderCoordinateBasis a := by
  fin_cases a <;> simp [roundCylinderCoordinateBasis, sign]

def pullback (B : RoundCylinderTwoTensor) : RoundCylinderTwoTensor :=
  fun z v w => B (space z) (v.1, -v.2) (w.1, -w.2)

theorem coefficient_pullback (B : RoundCylinderTwoTensor)
    (hB : ∀ (z : RoundCylinderSpace) (a b : ℝ) (v w : RoundCylinderTangent z),
      B z (a • v) (b • w) = a * b * B z v w)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderTensorCoefficient (pullback B) c p a b =
      sign a * sign b * roundCylinderTensorCoefficient B c (coordinates p) a b := by
  have hv (i : Fin 3) :
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
        -(roundCylinderCoordinateBasis i).2) =
      sign i • (mfderiv (𝓡 2) (𝓡 2) c.symm p.1
        (roundCylinderCoordinateBasis i).1, (roundCylinderCoordinateBasis i).2) := by
    fin_cases i <;> simp [roundCylinderCoordinateBasis, sign]
  unfold roundCylinderTensorCoefficient pullback
  dsimp only [space, coordinates_apply]
  rw [hv a, hv b, hB]

theorem fderiv_reflect (f : RoundCylinderCoordinates → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin 3) :
    fderiv ℝ (fun q => f (coordinates q)) p (roundCylinderCoordinateBasis a) =
      sign a * fderiv ℝ f (coordinates p) (roundCylinderCoordinateBasis a) := by
  change fderiv ℝ (f ∘ coordinates) p _ = _
  rw [coordinates.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    coordinates_basis, map_smul, smul_eq_mul]

theorem fderiv_const_mul_reflect (s : ℝ) (f : RoundCylinderCoordinates → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin 3) :
    fderiv ℝ (fun q => s * f (coordinates q)) p (roundCylinderCoordinateBasis a) =
      s * sign a * fderiv ℝ f (coordinates p) (roundCylinderCoordinateBasis a) := by
  change fderiv ℝ (s • (f ∘ coordinates)) p _ = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, Function.comp_def]
  rw [fderiv_reflect]
  ring

end PoincareConjecture.RoundCylinderReflection

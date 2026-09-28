import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderTimeComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M45

open M36 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

def cylinderAxialReflection (z : RoundCylinderSpace) : RoundCylinderSpace :=
  (z.1, -z.2)

noncomputable def cylinderCoordinateReflection : V ≃L[ℝ] V :=
  (ContinuousLinearEquiv.refl ℝ E₂).prodCongr (ContinuousLinearEquiv.neg ℝ)

def cylinderReflectionSign : Fin 3 → ℝ := ![1, 1, -1]

@[simp] theorem cylinderCoordinateReflection_apply (p : V) :
    cylinderCoordinateReflection p = (p.1, -p.2) := rfl

@[simp] theorem cylinderReflectionSign_sq (a : Fin 3) :
    cylinderReflectionSign a ^ 2 = 1 := by
  fin_cases a <;> norm_num [cylinderReflectionSign]

theorem cylinderCoordinateReflection_basis (a : Fin 3) :
    cylinderCoordinateReflection (roundCylinderCoordinateBasis a) =
      cylinderReflectionSign a • roundCylinderCoordinateBasis a := by
  fin_cases a <;> simp [roundCylinderCoordinateBasis, cylinderReflectionSign]

noncomputable def cylinderReflectedTensor (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor :=
  fun z v w => B (cylinderAxialReflection z) (v.1, -v.2) (w.1, -w.2)

theorem cylinderReflectedTensor_coefficient (B : RoundCylinderTwoTensor)
    (hB : ∀ z, IsBilinearMap ℝ (B z))
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : V) (a b : Fin 3) :
    roundCylinderTensorCoefficient (cylinderReflectedTensor B) c p a b =
      cylinderReflectionSign a * cylinderReflectionSign b *
        roundCylinderTensorCoefficient B c (cylinderCoordinateReflection p) a b := by
  have hslot (i : Fin 3) :
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
        -(roundCylinderCoordinateBasis i).2) =
      cylinderReflectionSign i •
        (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
          (roundCylinderCoordinateBasis i).2) := by
    fin_cases i <;> simp [roundCylinderCoordinateBasis, cylinderReflectionSign]
  unfold roundCylinderTensorCoefficient cylinderReflectedTensor
  dsimp only [cylinderAxialReflection, cylinderCoordinateReflection_apply]
  rw [hslot, hslot]
  rw [(hB _).smul_left, (hB _).smul_right]
  simp only [smul_eq_mul]
  ring

theorem cylinderReflection_gram (t : ℝ) (theta : UnitTwoSphere) (p : V)
    (a b : Fin 3) :
    roundCylinderGram t (chartAt E₂ theta) p a b =
      cylinderReflectionSign a * cylinderReflectionSign b *
        roundCylinderGram t (chartAt E₂ theta) (cylinderCoordinateReflection p) a b := by
  simp only [evolving_roundCylinderGram_chart, cylinderCoordinateReflection_apply,
    cylinderSphereFactor]
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.diagonal, cylinderReflectionSign]

theorem cylinderReflection_christoffel {t : ℝ} (ht : t < 1)
    (theta : UnitTwoSphere) (p : V) (a b c : Fin 3) :
    roundCylinderChristoffel t (chartAt E₂ theta) p a b c =
      cylinderReflectionSign a * cylinderReflectionSign b * cylinderReflectionSign c *
        roundCylinderChristoffel t (chartAt E₂ theta)
          (cylinderCoordinateReflection p) a b c := by
  simp only [evolving_roundCylinderChristoffel_eq ht, roundCylinderChristoffel_chart,
    cylinderCoordinateReflection_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [cylinderReflectionSign, cylinderChristoffelLinear,
      cylinderHorizontalCovector, cylinderHorizontalGram, roundCylinderCoordinateBasis]

end PoincareConjecture.M45

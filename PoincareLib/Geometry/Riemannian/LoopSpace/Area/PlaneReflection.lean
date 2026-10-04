import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Boundary.CurveLipschitz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Reflection of the filling parameter disk

Morgan-Tian Definition 18.17, printed p. 430, boundary regularization.
Reflection fixes the first coordinate, negates the second, reverses
the angular parameter, and preserves the disk and its actual volume.
-/

set_option autoImplicit false

open Set

namespace PoincareMT

/-- Reflection in the first coordinate axis. Source: MT Definition
18.17, p. 430, reflected-disk derivation. -/
noncomputable def m60PlaneReflection : LoopPlane ≃ₗᵢ[ℝ] LoopPlane :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 2 =>
    if i = 0 then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)

/-- Explicit reflected coordinates. Source: MT Definition 18.17,
p. 430, reflected-disk derivation. -/
theorem m60PlaneReflection_apply (z : LoopPlane) (i : Fin 2) :
    m60PlaneReflection z i = if i = 0 then z i else -z i := by
  fin_cases i <;> simp [m60PlaneReflection]

/-- Reflection is its own inverse. Source: MT Definition 18.17,
p. 430, reflected-disk derivation. -/
theorem m60PlaneReflection_involutive : Function.Involutive m60PlaneReflection := by
  intro z
  ext i
  simp only [m60PlaneReflection_apply]
  split_ifs <;> simp

/-- Reflection reverses the angular parameter exactly. Source: MT
Definition 18.17, p. 430, reflected-disk derivation. -/
theorem m60PlaneReflection_angular (t : ℝ) :
    m60PlaneReflection (Proofs.M58.angularPoint t) = Proofs.M58.angularPoint (-t) := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, Proofs.M58.angularPoint]

/-- The first standard tangent vector is fixed by reflection. Source:
MT Definition 18.17, p. 430, reflected-area derivation. -/
theorem m60PlaneReflection_basis_zero :
    m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, EuclideanSpace.basisFun_apply]

/-- The second standard tangent vector is negated by reflection.
Source: MT Definition 18.17, p. 430, reflected-area derivation. -/
theorem m60PlaneReflection_basis_one :
    m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, EuclideanSpace.basisFun_apply]

/-- Reflection preserves the actual unit filling disk. Source: MT
Definition 18.17, p. 430, reflected-disk derivation. -/
theorem m60PlaneReflection_preimage_disk :
    m60PlaneReflection ⁻¹' loopDiskSet = loopDiskSet := by
  ext z
  simp only [mem_preimage, loopDiskSet, Metric.mem_closedBall, dist_zero_right,
    m60PlaneReflection.norm_map]

/-- The induced circle homeomorphism is the reflection parameter.
Source: MT Definition 18.17, p. 430, reflected-disk derivation. -/
noncomputable def m60CircleReflection : CircleReparameterization where
  map z := ⟨m60PlaneReflection z.val, (m60PlaneReflection.norm_map z.val).trans z.property⟩
  inverse z := ⟨m60PlaneReflection z.val, (m60PlaneReflection.norm_map z.val).trans z.property⟩
  left_inverse z := Subtype.ext (m60PlaneReflection_involutive z.val)
  right_inverse z := Subtype.ext (m60PlaneReflection_involutive z.val)
  continuous_map := by
    apply Continuous.subtype_mk
    exact m60PlaneReflection.continuous.comp continuous_subtype_val
  continuous_inverse := by
    apply Continuous.subtype_mk
    exact m60PlaneReflection.continuous.comp continuous_subtype_val

end PoincareMT

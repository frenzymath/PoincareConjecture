import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.BoundaryCurveLipschitz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false

open Set

namespace PoincareConjecture

noncomputable def m60PlaneReflection : LoopPlane ≃ₗᵢ[ℝ] LoopPlane :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 2 =>
    if i = 0 then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)

theorem m60PlaneReflection_apply (z : LoopPlane) (i : Fin 2) :
    m60PlaneReflection z i = if i = 0 then z i else -z i := by
  fin_cases i <;> simp [m60PlaneReflection]

theorem m60PlaneReflection_involutive : Function.Involutive m60PlaneReflection := by
  intro z
  ext i
  simp only [m60PlaneReflection_apply]
  split_ifs <;> simp

theorem m60PlaneReflection_angular (t : ℝ) :
    m60PlaneReflection (Proofs.M58.angularPoint t) = Proofs.M58.angularPoint (-t) := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, Proofs.M58.angularPoint]

theorem m60PlaneReflection_basis_zero :
    m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, EuclideanSpace.basisFun_apply]

theorem m60PlaneReflection_basis_one :
    m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, EuclideanSpace.basisFun_apply]

theorem m60PlaneReflection_preimage_disk :
    m60PlaneReflection ⁻¹' loopDiskSet = loopDiskSet := by
  ext z
  simp only [mem_preimage, loopDiskSet, Metric.mem_closedBall, dist_zero_right,
    m60PlaneReflection.norm_map]

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

end PoincareConjecture

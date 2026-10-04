import PoincareLib.Geometry.Manifold.Circle.FlatCharts
import PoincareLib.Geometry.Manifold.LocalDiffeomorph
import PoincareLib.Topology.Manifold.NeckCap.Fibration.Quotient.Circle

/-!
# Additive quotient circles and the Euclidean unit circle

The standard exponential identifies a positive-period additive circle with
the unit sphere in Euclidean two-space. For any smooth atlas in which the
real quotient map is a local diffeomorphism, this identification is a smooth
diffeomorphism.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace AddCircle

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := Metric.sphere (0 : EuclideanSpace Real (Fin 2)) 1

/-- The canonical topological identification with the Euclidean unit circle. -/
def unitSphereHomeomorph {T : Real} (hT : 0 < T) : AddCircle T ≃ₜ S1 :=
  (homeomorphCircle hT.ne').trans PoincareMT.complexCircleDiffeomorph.toHomeomorph

@[simp]
theorem unitSphereHomeomorph_apply_coe {T : Real} (hT : 0 < T) (t : Real) :
    unitSphereHomeomorph hT (t : AddCircle T) = PoincareMT.unitCircleExp (t / T) := by
  change PoincareMT.complexCircleDiffeomorph (homeomorphCircle hT.ne' (t : AddCircle T)) = _
  rw [homeomorphCircle_apply, toCircle_apply_mk]
  unfold PoincareMT.unitCircleExp
  congr 2
  ring

/-- Smoothness of the quotient and its local inverse transfers the standard
exponential's local diffeomorphism property to any compatible circle atlas. -/
theorem isLocalDiffeomorph_unitSphereHomeomorph
    {T : Real} (hT : 0 < T) [ChartedSpace E1 (AddCircle T)]
    (hq : IsLocalDiffeomorph 𝓘(Real, Real) (𝓡 1) ∞
      (fun t : Real => (t : AddCircle T))) :
    IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ (unitSphereHomeomorph hT) := by
  let A : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ := {
    toEquiv := Equiv.mulRight₀ T⁻¹ (inv_ne_zero hT.ne')
    contMDiff_toFun := (contDiff_id.mul contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.mul contDiff_const).contMDiff }
  intro q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply (hq t).of_comp
  have h := (A.isLocalDiffeomorph t).comp (𝓡 1) S1
    (PoincareMT.isLocalDiffeomorph_unitCircleExp (A t))
  have heq : (unitSphereHomeomorph hT) ∘ (fun s : Real => (s : AddCircle T)) =
      PoincareMT.unitCircleExp ∘ A := by
    funext s
    simp only [comp_apply, unitSphereHomeomorph_apply_coe]
    rfl
  rw [heq]
  exact h

/-- The positive-period quotient circle with any atlas making its quotient
map a local diffeomorphism is diffeomorphic to the standard unit circle. -/
def unitSphereDiffeomorph
    {T : Real} (hT : 0 < T) [ChartedSpace E1 (AddCircle T)]
    (hq : IsLocalDiffeomorph 𝓘(Real, Real) (𝓡 1) ∞
      (fun t : Real => (t : AddCircle T))) :
    Diffeomorph (𝓡 1) (𝓡 1) (AddCircle T) S1 ∞ :=
  (isLocalDiffeomorph_unitSphereHomeomorph hT hq).diffeomorphOfBijective
    (unitSphereHomeomorph hT).bijective

@[simp]
theorem unitSphereDiffeomorph_apply_coe
    {T : Real} (hT : 0 < T) [ChartedSpace E1 (AddCircle T)]
    (hq : IsLocalDiffeomorph 𝓘(Real, Real) (𝓡 1) ∞
      (fun t : Real => (t : AddCircle T))) (t : Real) :
    unitSphereDiffeomorph hT hq (t : AddCircle T) = PoincareMT.unitCircleExp (t / T) :=
  unitSphereHomeomorph_apply_coe hT t

end AddCircle

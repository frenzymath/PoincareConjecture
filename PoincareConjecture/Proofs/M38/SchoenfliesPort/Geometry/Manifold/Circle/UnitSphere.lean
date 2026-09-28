import PoincareConjecture.Proofs.M38.SchoenfliesPort.FlatCircleCharts
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Circle







open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture

namespace M38Schoenflies










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace AddCircle

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := Metric.sphere (0 : EuclideanSpace Real (Fin 2)) 1


def unitSphereHomeomorph {T : Real} (hT : 0 < T) : AddCircle T ≃ₜ S1 :=
  (homeomorphCircle hT.ne').trans PoincareConjecture.complexCircleDiffeomorph.toHomeomorph

@[simp]
theorem unitSphereHomeomorph_apply_coe {T : Real} (hT : 0 < T) (t : Real) :
    unitSphereHomeomorph hT (t : AddCircle T) = PoincareConjecture.unitCircleExp (t / T) := by
  change PoincareConjecture.complexCircleDiffeomorph (homeomorphCircle hT.ne' (t : AddCircle T)) = _
  rw [homeomorphCircle_apply, toCircle_apply_mk]
  unfold PoincareConjecture.unitCircleExp
  congr 2
  ring



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
    (PoincareConjecture.isLocalDiffeomorph_unitCircleExp (A t))
  have heq : (unitSphereHomeomorph hT) ∘ (fun s : Real => (s : AddCircle T)) =
      PoincareConjecture.unitCircleExp ∘ A := by
    funext s
    simp only [comp_apply, unitSphereHomeomorph_apply_coe]
    rfl
  rw [heq]
  exact h



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
    unitSphereDiffeomorph hT hq (t : AddCircle T) = PoincareConjecture.unitCircleExp (t / T) :=
  unitSphereHomeomorph_apply_coe hT t

end AddCircle

end

end M38Schoenflies

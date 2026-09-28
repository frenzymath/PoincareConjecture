import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.PeriodicLoop
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.Relabeling
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

private noncomputable def complexLoopCircle : Circle ≃ₜ LoopCircle where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z,
    by rw [LinearIsometryEquiv.norm_map, z.norm_coe]⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z,
    mem_sphere_zero_iff_norm.mpr (by rw [LinearIsometryEquiv.norm_map, z.property])⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z)
  continuous_toFun :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => by
        change ‖Complex.orthonormalBasisOneI.repr (z : ℂ)‖ = 1
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp z.property)
  continuous_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => mem_sphere_zero_iff_norm.mpr (by
        change ‖Complex.orthonormalBasisOneI.repr.symm (z : LoopPlane)‖ = 1
        rw [LinearIsometryEquiv.norm_map, z.property]))

noncomputable def m65AngleLoopCircle : Real.Angle ≃ₜ LoopCircle :=
  AddCircle.homeomorphCircle'.trans complexLoopCircle

theorem m65AngleLoopCircle_coe (x : ℝ) :
    m65AngleLoopCircle (x : Real.Angle) =
      ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr (Circle.exp x : ℂ) = Proofs.M58.angularPoint x
  ext i
  fin_cases i <;> simp [Proofs.M58.angularPoint, Circle.coe_exp, Complex.exp_mul_I,
    Complex.orthonormalBasisOneI_repr_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem inverse_degree_one (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) (x : ℝ) :
    phi.symm (x + curvePeriod) = phi.symm x + curvePeriod := by
  apply phi.injective
  rw [phi.apply_symm_apply, hp, phi.apply_symm_apply]

private noncomputable def angleRelabeling (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) : Real.Angle ≃ₜ Real.Angle := by
  have hperiod : Function.Periodic (fun x : ℝ => (phi x : Real.Angle)) (2 * Real.pi) := by
    intro x
    change ((phi (x + curvePeriod) : ℝ) : Real.Angle) = _
    rw [hp, Real.Angle.coe_add]
    simp [curvePeriod]
  have hinverse : Function.Periodic (fun x : ℝ => (phi.symm x : Real.Angle))
      (2 * Real.pi) := by
    intro x
    change ((phi.symm (x + curvePeriod) : ℝ) : Real.Angle) = _
    rw [inverse_degree_one phi hp, Real.Angle.coe_add]
    simp [curvePeriod]
  exact {
    toFun := hperiod.lift
    invFun := hinverse.lift
    left_inv := fun x => QuotientAddGroup.induction_on x (fun y => by
      change ((phi.symm (phi y) : ℝ) : Real.Angle) = (y : Real.Angle)
      rw [phi.symm_apply_apply])
    right_inv := fun x => QuotientAddGroup.induction_on x (fun y => by
      change ((phi (phi.symm y) : ℝ) : Real.Angle) = (y : Real.Angle)
      rw [phi.apply_symm_apply])
    continuous_toFun := continuous_coinduced_dom.mpr
      ((AddCircle.continuous_mk' (2 * Real.pi)).comp phi.continuous)
    continuous_invFun := continuous_coinduced_dom.mpr
      ((AddCircle.continuous_mk' (2 * Real.pi)).comp phi.symm.continuous) }

noncomputable def m65CircleRelabeling (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) : LoopCircle ≃ₜ LoopCircle :=
  m65AngleLoopCircle.symm.trans ((angleRelabeling phi hp).trans m65AngleLoopCircle)

theorem m65CircleRelabeling_angular (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) (x : ℝ) :
    m65CircleRelabeling phi hp
        ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ =
      ⟨Proofs.M58.angularPoint (phi x), Proofs.M58.norm_angularPoint (phi x)⟩ := by
  rw [← m65AngleLoopCircle_coe x]
  change m65AngleLoopCircle ((angleRelabeling phi hp)
    (m65AngleLoopCircle.symm (m65AngleLoopCircle (x : Real.Angle)))) = _
  rw [m65AngleLoopCircle.symm_apply_apply]
  exact m65AngleLoopCircle_coe (phi x)

theorem m65AngularCircle_surjective : Function.Surjective (fun x : ℝ =>
    (⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ : LoopCircle)) := by
  have h (y : Real.Angle) : ∃ x : ℝ, m65AngleLoopCircle y =
      ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ :=
    QuotientAddGroup.induction_on y (fun x => ⟨x, m65AngleLoopCircle_coe x⟩)
  intro z
  obtain ⟨x, hx⟩ := h (m65AngleLoopCircle.symm z)
  exact ⟨x, hx.symm.trans (m65AngleLoopCircle.apply_symm_apply z)⟩

theorem m65AngularCircle_map_nhds (x : ℝ) :
    Filter.map (fun y : ℝ =>
      (⟨Proofs.M58.angularPoint y, Proofs.M58.norm_angularPoint y⟩ : LoopCircle)) (𝓝 x) =
      𝓝 (⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ : LoopCircle) := by
  have heq : (fun y : ℝ =>
      (⟨Proofs.M58.angularPoint y, Proofs.M58.norm_angularPoint y⟩ : LoopCircle)) =
      m65AngleLoopCircle ∘ (fun y : ℝ => (y : Real.Angle)) :=
    funext (fun y => (m65AngleLoopCircle_coe y).symm)
  rw [heq]
  rw [← m65AngleLoopCircle_coe x]
  exact (m65AngleLoopCircle.isOpenMap.comp QuotientAddGroup.isOpenMap_coe).map_nhds_eq
    ((m65AngleLoopCircle.continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).continuousAt)

theorem m65CircleRelabeling_loop_values
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (gamma eta : C1FreeLoopSpace (M := M))
    (he : ∀ x, periodicFreeLoop eta x = periodicFreeLoop gamma (phi x)) :
    ∀ z, eta z = gamma (m65CircleRelabeling phi hp z) := by
  intro z
  obtain ⟨x, rfl⟩ := m65AngularCircle_surjective z
  rw [m65CircleRelabeling_angular]
  exact (eta.boundary ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩).symm.trans
    ((he x).trans (gamma.boundary
      ⟨Proofs.M58.angularPoint (phi x), Proofs.M58.norm_angularPoint (phi x)⟩))

end PoincareConjecture

import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.PeriodicLoop
import PoincareLib.Geometry.CurveShortening.Deformation.AreaContinuity.Relabeling
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The genuine circle homeomorphism of a real relabeling

An actual degree-one order isomorphism lifts to inverse continuous
maps of the angle quotient. The fixed real 1,I coordinates transport
them to the contract's parameter circle. This supplies the actual
same-disk relabeling in Claim 19.28, MT pp. 459-461; derivation 37.
-/

set_option autoImplicit false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareMT

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

/-- The actual angle quotient is homeomorphic to the frozen parameter
circle via its genuine angular map. MT p. 430; derivation 37. -/
noncomputable def m65AngleLoopCircle : Real.Angle ≃ₜ LoopCircle :=
  AddCircle.homeomorphCircle'.trans complexLoopCircle

/-- The quotient homeomorphism evaluates to the literal angular point.
MT p. 430 and Claim 19.28, p. 460; derivation 37. -/
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

/-- A genuine degree-one real order isomorphism induces a genuine
parameter-circle homeomorphism, retaining its actual inverse.
Claim 19.28, MT pp. 459-461; derivation 37. -/
noncomputable def m65CircleRelabeling (phi : ℝ ≃o ℝ)
    (hp : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) : LoopCircle ≃ₜ LoopCircle :=
  m65AngleLoopCircle.symm.trans ((angleRelabeling phi hp).trans m65AngleLoopCircle)

/-- Circle relabeling is the original real relabeling on every angular
parameter. Claim 19.28, MT pp. 459-461; derivation 37. -/
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

/-- The genuine angular parametrization covers the entire frozen
circle. MT p. 430; derivation 37. -/
theorem m65AngularCircle_surjective : Function.Surjective (fun x : ℝ =>
    (⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ : LoopCircle)) := by
  have h (y : Real.Angle) : ∃ x : ℝ, m65AngleLoopCircle y =
      ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ :=
    QuotientAddGroup.induction_on y (fun x => ⟨x, m65AngleLoopCircle_coe x⟩)
  intro z
  obtain ⟨x, hx⟩ := h (m65AngleLoopCircle.symm z)
  exact ⟨x, hx.symm.trans (m65AngleLoopCircle.apply_symm_apply z)⟩

/-- Angular neighborhoods push forward to the actual circle
neighborhoods, including the cut of the principal argument.
Claim 19.28, MT pp. 460-461; derivation 37. -/
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

/-- Equality after the actual real relabeling is equality after the
constructed circle homeomorphism. The existing same-disk transport
therefore applies. Claim 19.28, MT pp. 459-461; derivation 37. -/
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

end PoincareMT

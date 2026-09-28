import PoincareConjecture.Proofs.M60.Mathlib.HomeomorphismLift
import PoincareConjecture.Proofs.M60.Mathlib.CircleLiftPeriod
import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace PoincareConjecture

noncomputable def m60LoopCircleHomeomorphCircle : LoopCircle ≃ₜ Circle where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z.val, by
    change Complex.orthonormalBasisOneI.repr.symm z.val ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right,
      Complex.orthonormalBasisOneI.repr.symm.norm_map, z.property]⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr (z : ℂ), by
    rw [Complex.orthonormalBasisOneI.repr.norm_map, Circle.norm_coe]⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z.val)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply (z : ℂ))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val

theorem m60LoopCircleHomeomorphCircle_angular (t : ℝ) :
    m60LoopCircleHomeomorphCircle
      ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ = Circle.exp t := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr.symm (Proofs.M58.angularPoint t) = (Circle.exp t : ℂ)
  rw [Complex.orthonormalBasisOneI_repr_symm_apply, Circle.coe_exp]
  change (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I = Complex.exp (t * Complex.I)
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem m60_exists_circle_reparameterization_lift (sigma : CircleReparameterization) :
    ∃ H : ℝ ≃ₜ ℝ,
      (∀ t : ℝ,
        (⟨Proofs.M58.angularPoint (H t), Proofs.M58.norm_angularPoint (H t)⟩ : LoopCircle) =
          sigma.map ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩) ∧
      (StrictMono H ∨ StrictAnti H) := by
  let e : LoopCircle ≃ₜ LoopCircle :=
    { toFun := sigma.map
      invFun := sigma.inverse
      left_inv := sigma.left_inverse
      right_inv := sigma.right_inverse
      continuous_toFun := sigma.continuous_map
      continuous_invFun := sigma.continuous_inverse }
  let c := m60LoopCircleHomeomorphCircle
  let e' : Circle ≃ₜ Circle := (c.symm.trans e).trans c
  obtain ⟨b, hb⟩ := Circle.exp_surjective (e' (Circle.exp 0))
  obtain ⟨H, _, hH⟩ := M60.exists_homeomorph_lift Circle.isCoveringMap_exp e' 0 b hb
  refine ⟨H, ?_, H.continuous.strictMono_of_inj H.injective⟩
  intro t
  apply c.injective
  rw [m60LoopCircleHomeomorphCircle_angular]
  have hc : c.symm (Circle.exp t) =
      ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ := by
    apply c.injective
    rw [c.apply_symm_apply, m60LoopCircleHomeomorphCircle_angular]
  have hh := hH t
  dsimp only [e', Homeomorph.trans_apply] at hh
  rw [hc] at hh
  exact hh

theorem m60CircleLift_period (sigma : CircleReparameterization) (H : ℝ ≃ₜ ℝ)
    (hlift : ∀ t : ℝ,
      (⟨Proofs.M58.angularPoint (H t), Proofs.M58.norm_angularPoint (H t)⟩ : LoopCircle) =
        sigma.map ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩) :
    (StrictMono H ∧ ∀ t, H (t + rampPeriod) = H t + rampPeriod) ∨
      (StrictAnti H ∧ ∀ t, H (t + rampPeriod) = H t - rampPeriod) := by
  let c := m60LoopCircleHomeomorphCircle
  let e : Circle → Circle := fun z => c (sigma.map (c.symm z))
  have he : Function.Injective e :=
    c.injective.comp (sigma.left_inverse.injective.comp c.symm.injective)
  have hcomplex (t : ℝ) : Circle.exp (H t) = e (Circle.exp t) := by
    rw [← m60LoopCircleHomeomorphCircle_angular (H t), hlift]
    dsimp only [e]
    rw [← m60LoopCircleHomeomorphCircle_angular t, c.symm_apply_apply]
  rcases H.continuous.strictMono_of_inj H.injective with hmono | hanti
  · exact Or.inl ⟨hmono, fun t =>
      M60.circle_lift_add_two_pi_of_strictMono he H.continuous hmono hcomplex t⟩
  · exact Or.inr ⟨hanti, fun t =>
      M60.circle_lift_add_two_pi_of_strictAnti he H.continuous hanti hcomplex t⟩

end PoincareConjecture

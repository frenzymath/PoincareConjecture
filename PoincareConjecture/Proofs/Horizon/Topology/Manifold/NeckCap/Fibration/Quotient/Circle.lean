import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Models
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

local instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩

noncomputable def complexCircleDiffeomorph :
    Diffeomorph (𝓡 1) (𝓡 1) Circle UnitCircle ∞ where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
      using z.norm_coe⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z, by
    change Complex.orthonormalBasisOneI.repr.symm z ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
      using z.property⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z)
  contMDiff_toFun := (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.comp
    (contMDiff_coe_sphere (n := 1))).codRestrict_sphere (n := 1) (fun z => by
      simpa only [comp_apply, Metric.mem_sphere, dist_zero_right,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.norm_map] using z.property)
  contMDiff_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (n := 1))).codRestrict_sphere (n := 1) (fun z => by
        simpa only [comp_apply, Metric.mem_sphere, dist_zero_right,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.norm_map] using z.property)

noncomputable def unitCircleExp (t : ℝ) : UnitCircle :=
  complexCircleDiffeomorph (Circle.exp ((2 * Real.pi) * t))

theorem contMDiff_unitCircleExp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ unitCircleExp :=
  complexCircleDiffeomorph.contMDiff.comp
    (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff)

theorem unitCircleExp_surjective : Surjective unitCircleExp := by
  intro z
  obtain ⟨t, ht⟩ := Circle.exp_surjective (complexCircleDiffeomorph.symm z)
  refine ⟨t / (2 * Real.pi), ?_⟩
  dsimp [unitCircleExp]
  rw [mul_div_cancel₀ _ (ne_of_gt Real.two_pi_pos), ht,
    complexCircleDiffeomorph.apply_symm_apply]

theorem unitCircleExp_eq_iff {s t : ℝ} :
    unitCircleExp s = unitCircleExp t ↔ ∃ n : ℤ, s = t + n := by
  change complexCircleDiffeomorph.toEquiv (Circle.exp ((2 * Real.pi) * s)) =
    complexCircleDiffeomorph.toEquiv (Circle.exp ((2 * Real.pi) * t)) ↔ _
  rw [complexCircleDiffeomorph.toEquiv.injective.eq_iff, Circle.exp_eq_exp]
  apply exists_congr
  intro n
  constructor
  · intro h
    nlinarith [Real.pi_pos]
  · intro h
    rw [h]
    ring

theorem unitCircleExp_periodic : Periodic unitCircleExp 1 := by
  intro t
  exact unitCircleExp_eq_iff.mpr ⟨1, by simp⟩

theorem unitCircleExp_add_int (t : ℝ) (n : ℤ) :
    unitCircleExp (t + n) = unitCircleExp t :=
  unitCircleExp_eq_iff.mpr ⟨n, rfl⟩

theorem isCoveringMap_unitCircleExp : IsCoveringMap unitCircleExp := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ (2 * Real.pi) (ne_of_gt Real.two_pi_pos))
  exact (Circle.isCoveringMap_exp.comp_homeomorph e).homeomorph_comp
    complexCircleDiffeomorph.toHomeomorph

theorem isLocalDiffeomorph_circleExp : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp := by
  intro a
  let V : Set Circle := {z | ((z / Circle.exp a : Circle) : ℂ) ∈ Complex.slitPlane}
  have hrotate : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle => (z : ℂ) / (Circle.exp a : ℂ)) :=
    (contDiff_id.div_const _).contMDiff.comp (contMDiff_coe_sphere (n := 1))
  let P : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ Circle ∞ := {
    toFun := Circle.exp
    invFun := fun z => a + Complex.arg (z / Circle.exp a : Circle)
    source := Ioo (a - Real.pi) (a + Real.pi)
    target := V
    map_source' := by
      intro t ht
      change ((Circle.exp t / Circle.exp a : Circle) : ℂ) ∈ Complex.slitPlane
      rw [← Circle.exp_sub, Circle.coe_exp]
      apply Complex.expOpenPartialHomeomorph.map_source
      change (-(Real.pi) < (((t - a : ℝ) : ℂ) * Complex.I).im) ∧
        ((((t - a : ℝ) : ℂ) * Complex.I).im < Real.pi)
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
      constructor <;> linarith [ht.1, ht.2]
    map_target' := by
      intro z hz
      have hlo := Complex.neg_pi_lt_arg ((z / Circle.exp a : Circle) : ℂ)
      have hhi := lt_of_le_of_ne (Complex.arg_le_pi ((z / Circle.exp a : Circle) : ℂ))
        (Complex.slitPlane_arg_ne_pi hz)
      constructor <;> linarith
    left_inv' := by
      intro t ht
      rw [← Circle.exp_sub, Circle.arg_exp (by linarith [ht.1]) (by linarith [ht.2])]
      ring
    right_inv' := by
      intro z _
      rw [Circle.exp_add, Circle.exp_arg]
      simp [div_eq_mul_inv, mul_left_comm]
    open_source := isOpen_Ioo
    open_target := Complex.isOpen_slitPlane.preimage hrotate.continuous
    contMDiffOn_toFun := contMDiff_circleExp.contMDiffOn
    contMDiffOn_invFun := by
      intro z hz
      have hlog : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
          (fun z : Circle => Complex.log ((z : ℂ) / (Circle.exp a : ℂ))) z :=
        ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contMDiffAt.comp z (hrotate z)
      have him := Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z hlog
      have harg : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
          (fun z : Circle => Complex.arg (z / Circle.exp a : Circle)) z := by
        change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
          (fun z : Circle => (Complex.log ((z : ℂ) / (Circle.exp a : ℂ))).im) z at him
        simpa only [Complex.log_im, Circle.coe_div] using him
      exact ((contDiff_const.add contDiff_id).contMDiff.contMDiffAt.comp z harg).contMDiffWithinAt }
  exact ⟨P, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
    fun _ _ => rfl⟩

theorem isLocalDiffeomorph_unitCircleExp :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ unitCircleExp := by
  let e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := Equiv.mulLeft₀ (2 * Real.pi) (ne_of_gt Real.two_pi_pos)
    contMDiff_toFun := (contDiff_const.mul contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_const.mul contDiff_id).contMDiff }
  intro t
  exact ((e.isLocalDiffeomorph t).comp (𝓡 1) Circle
    (isLocalDiffeomorph_circleExp (e t))).comp (𝓡 1) UnitCircle
      (complexCircleDiffeomorph.isLocalDiffeomorph (Circle.exp (e t)))

end PoincareConjecture

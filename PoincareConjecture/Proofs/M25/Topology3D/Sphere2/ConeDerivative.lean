import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialCalculus

set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

noncomputable def sphereConeExtension (q0 : UnitTwoSphere)
    (f : UnitTwoSphere → UnitTwoSphere) (x : E3) : E3 :=
  ‖x‖ • (f (unitRadialProjection q0 x) : E3)

@[simp] theorem sphereConeExtension_apply_sphere (q0 q : UnitTwoSphere)
    (f : UnitTwoSphere → UnitTwoSphere) :
    sphereConeExtension q0 f (q : E3) = (f q : E3) := by
  simp only [sphereConeExtension, norm_eq_of_mem_sphere q,
    unitRadialProjection_apply_coe, one_smul]

@[simp] theorem norm_sphereConeExtension (q0 : UnitTwoSphere)
    (f : UnitTwoSphere → UnitTwoSphere) (x : E3) :
    ‖sphereConeExtension q0 f x‖ = ‖x‖ := by
  rw [sphereConeExtension, norm_smul, Real.norm_of_nonneg (norm_nonneg x),
    norm_eq_of_mem_sphere, mul_one]

theorem sphereConeExtension_pos_smul (q0 : UnitTwoSphere)
    (f : UnitTwoSphere → UnitTwoSphere) {a : ℝ} (ha : 0 < a) (x : E3) :
    sphereConeExtension q0 f (a • x) = a • sphereConeExtension q0 f x := by
  rw [sphereConeExtension, unitRadialProjection_pos_smul q0 ha,
    norm_smul, Real.norm_of_nonneg ha.le, mul_smul]
  rfl

theorem sphereConeExtension_symm_apply_apply (q0 : UnitTwoSphere)
    (f : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) (x : E3) :
    sphereConeExtension q0 f.symm (sphereConeExtension q0 f x) = x := by
  by_cases hx : x = 0
  · simp only [hx, sphereConeExtension, norm_zero, zero_smul]
  change ‖sphereConeExtension q0 f x‖ •
    (f.symm (unitRadialProjection q0 (sphereConeExtension q0 f x)) : E3) = x
  rw [norm_sphereConeExtension, sphereConeExtension,
    unitRadialProjection_pos_smul q0 (norm_pos_iff.mpr hx),
    unitRadialProjection_apply_coe, f.symm_apply_apply,
    unitRadialProjection_coe_of_ne_zero q0 hx, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem contDiffAt_sphereConeExtension (q0 : UnitTwoSphere)
    (f : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) {x : E3} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (sphereConeExtension q0 f) x := by
  have hπ := (contMDiffOn_unitRadialProjection (n := 2) (m := ∞) q0).contMDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds (show x ∈ ({0} : Set E3)ᶜ from hx))
  have hF : ContDiffAt ℝ ∞
      (fun y : E3 => (f (unitRadialProjection q0 y) : E3)) x :=
    (((contMDiff_coe_sphere (n := 2) (m := ∞)).comp f.contMDiff).contMDiffAt.comp x
      hπ).contDiffAt
  exact (contDiffAt_norm ℝ hx).smul hF

theorem exists_sphereConeExtension_derivative_equiv (q0 p : UnitTwoSphere)
    (f : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) :
    ∃ L : E3 ≃L[ℝ] E3,
      (L : E3 →L[ℝ] E3) = fderiv ℝ (sphereConeExtension q0 f) (p : E3) ∧
      L (p : E3) = (f p : E3) := by
  let R := sphereConeExtension q0 f
  let S := sphereConeExtension q0 f.symm
  have hRp : R (p : E3) = (f p : E3) := sphereConeExtension_apply_sphere q0 p f
  have hSp : S (f p : E3) = (p : E3) := by
    simp only [S, sphereConeExtension_apply_sphere, f.symm_apply_apply]
  have hR : DifferentiableAt ℝ R (p : E3) :=
    (contDiffAt_sphereConeExtension q0 f (ne_zero_of_mem_unit_sphere p)).differentiableAt
      (by simp)
  have hS : DifferentiableAt ℝ S (f p : E3) :=
    (contDiffAt_sphereConeExtension q0 f.symm
      (ne_zero_of_mem_unit_sphere (f p))).differentiableAt (by simp)
  have hSR : S ∘ R = id := funext (sphereConeExtension_symm_apply_apply q0 f)
  have hRS : R ∘ S = id := funext (sphereConeExtension_symm_apply_apply q0 f.symm)
  have hleft : (fderiv ℝ S (f p : E3)).comp (fderiv ℝ R (p : E3)) =
      ContinuousLinearMap.id ℝ E3 := by
    rw [← hRp, ← fderiv_comp (p : E3) (hRp.symm ▸ hS) hR, hSR, fderiv_id]
  have hright : (fderiv ℝ R (p : E3)).comp (fderiv ℝ S (f p : E3)) =
      ContinuousLinearMap.id ℝ E3 := by
    rw [← hSp, ← fderiv_comp (f p : E3) (hSp.symm ▸ hR) hS, hRS, fderiv_id]
  let L := ContinuousLinearEquiv.equivOfInverse'
    (fderiv ℝ R (p : E3)) (fderiv ℝ S (f p : E3)) hright hleft
  refine ⟨L, rfl, ?_⟩
  have heq : (fun t : ℝ => R (t • (p : E3))) =ᶠ[𝓝 1] (fun t => t • R (p : E3)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with t ht
    exact sphereConeExtension_pos_smul q0 f ht p
  have hlinear := ((hasDerivAt_id (1 : ℝ)).smul_const (R (p : E3))).congr_of_eventuallyEq heq
  have hcone := hR.hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ)
    ((hasDerivAt_id (1 : ℝ)).smul_const (p : E3)) (by simp)
  change fderiv ℝ R (p : E3) (p : E3) = (f p : E3)
  simpa only [one_smul, hRp] using hcone.unique hlinear

end PoincareConjecture.M25.Topology3D

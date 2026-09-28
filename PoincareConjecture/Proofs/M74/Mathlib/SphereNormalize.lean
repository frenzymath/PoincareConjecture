import PoincareConjecture.Definitions.Ch15.SurgeryTopology

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M74

noncomputable def sphereNormalize (q0 : UnitTwoSphere) (x : StandardCapSpace) :
    UnitTwoSphere := by
  classical
  exact if h : x = 0 then q0 else
    ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr h)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩

theorem sphereNormalize_contMDiffAt (q0 : UnitTwoSphere) {x : StandardCapSpace}
    (hx : x ≠ 0) : ContMDiffAt (𝓡 3) (𝓡 2) ∞ (sphereNormalize q0) x := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  let U : TopologicalSpace.Opens StandardCapSpace := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hne (y : U) : (y : StandardCapSpace) ≠ 0 := y.2
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : U => ‖(y : StandardCapSpace)‖) :=
    fun y => ((contDiffAt_norm ℝ (hne y)).contMDiffAt).comp y contMDiff_subtype_val.contMDiffAt
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : U => ‖(y : StandardCapSpace)‖⁻¹ • (y : StandardCapSpace)) :=
    (hn.inv₀ (fun y => norm_ne_zero_iff.mpr (hne y))).smul contMDiff_subtype_val
  have hunit (y : U) : ‖(y : StandardCapSpace)‖⁻¹ • (y : StandardCapSpace) ∈
      sphere (0 : StandardCapSpace) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hne y))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne y))]
  have hdir : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun y : U => sphereNormalize q0 (y : StandardCapSpace)) := by
    have heq (y : U) : sphereNormalize q0 (y : StandardCapSpace) =
        ⟨‖(y : StandardCapSpace)‖⁻¹ • (y : StandardCapSpace), hunit y⟩ := by
      simp only [sphereNormalize, dif_neg (hne y)]
    simp_rw [heq]
    exact hf.codRestrict_sphere hunit
  exact (contMDiffAt_subtype_iff (U := U) (f := sphereNormalize q0) (x := ⟨x, hx⟩)).mp
    hdir.contMDiffAt

theorem sphereNormalize_pos_smul (q0 q : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    sphereNormalize q0 (r • q.1) = q := by
  have hqnorm : ‖q.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
  have hn : ‖r • q.1‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hqnorm, mul_one]
  have hne : r • q.1 ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hr)
  apply Subtype.ext
  simp only [sphereNormalize, dif_neg hne]
  rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]

end PoincareConjecture.M74

import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

def puncturedThreeSpace : Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩

def sphereCylinderDiffeomorphPunctured :
    Diffeomorph CylModel (𝓡 3) (S2 × ℝ) puncturedThreeSpace ∞ := by
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let f : S2 × ℝ → puncturedThreeSpace := fun p =>
    ⟨Real.exp p.2 • (p.1 : E3),
      smul_ne_zero (Real.exp_ne_zero _) (ne_zero_of_mem_unit_sphere p.1)⟩
  let g : puncturedThreeSpace → S2 × ℝ := fun x =>
    (⟨‖(x : E3)‖⁻¹ • (x : E3), by
      have hx : (x : E3) ≠ 0 := x.property
      simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩,
      Real.log ‖(x : E3)‖)
  have hnorm (q : S2) : ‖(q : E3)‖ = 1 := by
    simp
  have hleft : Function.LeftInverse g f := by
    rintro ⟨q, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [g, f, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
        hnorm, smul_smul, Real.exp_ne_zero]
    · simp [g, f, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), hnorm]
  have hright : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    have hx : (x : E3) ≠ 0 := x.property
    simp [f, g, Real.exp_log (norm_pos_iff.mpr hx), smul_smul,
      norm_ne_zero_iff.mpr hx]
  have hf : ContMDiff CylModel (𝓡 3) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff puncturedThreeSpace f).mp
    exact (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  have hg : ContMDiff (𝓡 3) CylModel ∞ g := by
    have hv : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : puncturedThreeSpace => (x : E3)) :=
      contMDiff_subtype_val
    have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : puncturedThreeSpace => ‖(x : E3)‖) := by
      intro x
      exact ((contDiffAt_norm ℝ (show (x : E3) ≠ 0 from x.property)).contMDiffAt).comp
        x hv.contMDiffAt
    apply ContMDiff.prodMk
    · apply ContMDiff.codRestrict_sphere
      exact (hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul hv
    · intro x
      exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).contMDiffAt.comp
        x hn.contMDiffAt
  exact ⟨⟨f, g, hleft, hright⟩, hf, hg⟩

@[simp] theorem sphereCylinderDiffeomorphPunctured_apply (p : S2 × ℝ) :
    (sphereCylinderDiffeomorphPunctured p : E3) = Real.exp p.2 • (p.1 : E3) := rfl

@[simp] theorem sphereCylinderDiffeomorphPunctured_zero (q : S2) :
    (sphereCylinderDiffeomorphPunctured (q, 0) : E3) = q := by
  simp

end Poincare

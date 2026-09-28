import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def unitRadialProjection (q0 : sphere (0 : E) 1) (x : E) :
    sphere (0 : E) 1 := by
  classical
  exact if hx : x = 0 then q0 else
    ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

@[simp] theorem unitRadialProjection_zero (q0 : sphere (0 : E) 1) :
    unitRadialProjection q0 0 = q0 := by
  simp [unitRadialProjection]

theorem unitRadialProjection_coe_of_ne_zero (q0 : sphere (0 : E) 1)
    {x : E} (hx : x ≠ 0) :
    (unitRadialProjection q0 x : E) = ‖x‖⁻¹ • x := by
  simp [unitRadialProjection, hx]

@[simp] theorem unitRadialProjection_apply_coe (q0 q : sphere (0 : E) 1) :
    unitRadialProjection q0 (q : E) = q := by
  apply Subtype.ext
  rw [unitRadialProjection_coe_of_ne_zero q0 (ne_zero_of_mem_unit_sphere q)]
  simp [norm_eq_of_mem_sphere q]

noncomputable def radialFamilyExtension {G : Type*} (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → G) (p : ℝ × E) : G :=
  c p.1 (unitRadialProjection q0 p.2)

@[simp] theorem radialFamilyExtension_apply_sphere {G : Type*}
    (q0 : sphere (0 : E) 1) (c : ℝ → sphere (0 : E) 1 → G)
    (z : ℝ) (q : sphere (0 : E) 1) :
    radialFamilyExtension q0 c (z, (q : E)) = c z q := by
  simp [radialFamilyExtension]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] {m : ℕ∞ω}

theorem contMDiffOn_unitRadialProjection (q0 : sphere (0 : E) 1) :
    ContMDiffOn 𝓘(ℝ, E) (𝓡 n) m (unitRadialProjection q0) ({0} : Set E)ᶜ := by
  let U : TopologicalSpace.Opens E := ⟨({0} : Set E)ᶜ, isClosed_singleton.isOpen_compl⟩
  have hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m (fun x : U => ‖(x : E)‖⁻¹ • (x : E)) := by
    intro x
    have hx : (x : E) ≠ 0 := x.2
    exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
      contDiffAt_id).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
  have hunit : ∀ x : U, ‖(x : E)‖⁻¹ • (x : E) ∈ sphere (0 : E) 1 := by
    intro x
    rw [← unitRadialProjection_coe_of_ne_zero q0 (show (x : E) ≠ 0 from x.2)]
    exact (unitRadialProjection q0 (x : E)).2
  have hS : ContMDiff 𝓘(ℝ, E) (𝓡 n) m (fun x : U => unitRadialProjection q0 (x : E)) := by
    have heq : (fun x : U => unitRadialProjection q0 (x : E)) =
        (fun x : U => (⟨‖(x : E)‖⁻¹ • (x : E), hunit x⟩ : sphere (0 : E) 1)) := by
      funext x
      apply Subtype.ext
      exact unitRadialProjection_coe_of_ne_zero q0 (show (x : E) ≠ 0 from x.2)
    rw [heq]
    exact hR.codRestrict_sphere (n := n) hunit
  intro x hx
  exact ((contMDiffAt_subtype_iff (U := U) (f := unitRadialProjection q0)
    (x := ⟨x, hx⟩)).mp (hS ⟨x, hx⟩)).contMDiffWithinAt

theorem contDiffOn_radialFamilyExtension {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q0 : sphere (0 : E) 1) (c : ℝ → sphere (0 : E) 1 → F)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, F) m
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2)) :
    ContDiffOn ℝ m (radialFamilyExtension q0 c) (univ ×ˢ ({0} : Set E)ᶜ) := by
  have hproj : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) m
      (fun p : ℝ × E => unitRadialProjection q0 p.2) (univ ×ˢ ({0} : Set E)ᶜ) :=
    (contMDiffOn_unitRadialProjection (n := n) q0).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hx => hx.2)
  exact (hc.comp_contMDiffOn (contDiff_fst.contMDiff.contMDiffOn.prodMk hproj)).contDiffOn

end InnerProduct

end PoincareConjecture.M25.Topology3D

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Analysis.InnerProductSpace.Calculus



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleCollar

abbrev Plane := EuclideanSpace Real (Fin 2)
abbrev Circle := sphere (0 : Plane) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : Fact (Module.finrank Real Plane = 1 + 1) := ⟨by simp⟩
instance : ChartedSpace (EuclideanSpace Real (Fin 1) × Real) (Circle × Real) :=
  prodChartedSpace _ _ _ _

def direction (x : Plane) : Circle := by
  classical
  exact if hx : x = 0 then ⟨EuclideanSpace.single 0 1, by simp⟩
    else ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem direction_coe {x : Plane} (hx : x ≠ 0) :
    (direction x : Plane) = ‖x‖⁻¹ • x := by simp [direction, hx]

theorem direction_smul (p : Circle) {ρ : Real} (hρ : 0 < ρ) :
    direction (ρ • (p : Plane)) = p := by
  apply Subtype.ext
  rw [direction_coe (smul_ne_zero hρ.ne' (ne_zero_of_mem_unit_sphere p))]
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, smul_smul, hρ.ne']

@[simp] theorem direction_circle (p : Circle) : direction p = p := by
  simpa using direction_smul p zero_lt_one

theorem contMDiffAt_direction {x : Plane} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 2) (𝓡 1) ∞ direction x := by
  let U : Opens Plane := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hn : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun y : U => ‖(y : Plane)‖) := by
    intro y
    exact (contDiffAt_norm Real y.property).contMDiffAt.comp y (contMDiff_subtype_val y)
  have hs : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun y : U => ‖(y : Plane)‖⁻¹ • (y : Plane)) :=
    (hn.inv₀ (fun y => norm_ne_zero_iff.mpr y.property)).smul contMDiff_subtype_val
  have hd : ContMDiff (𝓡 2) (𝓡 1) ∞ (fun y : U => direction y) := by
    have ht := hs.codRestrict_sphere (n := 1) (fun y => by
      rw [← direction_coe y.property]
      exact (direction y).property)
    apply ht.congr
    intro y
    exact Subtype.ext (direction_coe y.property)
  exact (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hd ⟨x, hx⟩)


def radial : PartialDiffeomorph (𝓡 2) Iprod Plane (Circle × Real) ∞ where
  toFun x := (direction x, ‖x‖ - 1)
  invFun z := (1 + z.2) • (z.1 : Plane)
  source := {0}ᶜ
  target := univ ×ˢ Ioi (-1)
  map_source' := by
    intro x hx
    refine ⟨mem_univ _, ?_⟩
    change -1 < ‖x‖ - 1
    have := norm_pos_iff.mpr hx
    linarith
  map_target' := by
    intro z hz
    have ht : -1 < z.2 := hz.2
    exact smul_ne_zero (by linarith : 1 + z.2 ≠ 0) (ne_zero_of_mem_unit_sphere z.1)
  left_inv' := by
    intro x hx
    change (1 + (‖x‖ - 1)) • (direction x : Plane) = x
    rw [direction_coe hx, show 1 + (‖x‖ - 1) = ‖x‖ by ring,
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  right_inv' := by
    intro z hz
    have ht : -1 < z.2 := hz.2
    have hpos : 0 < 1 + z.2 := by linarith
    apply Prod.ext
    · exact direction_smul z.1 hpos
    · change ‖(1 + z.2) • (z.1 : Plane)‖ - 1 = z.2
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  open_source := isClosed_singleton.isOpen_compl
  open_target := isOpen_univ.prod isOpen_Ioi
  contMDiffOn_toFun := by
    intro x hx
    exact ((contMDiffAt_direction hx).prodMk
      ((contDiffAt_norm Real hx).contMDiffAt.sub contMDiffAt_const)).contMDiffWithinAt
  contMDiffOn_invFun :=
    ((contMDiff_const.add contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)).contMDiffOn

@[simp] theorem radial_circle (p : Circle) : radial p = (p, 0) := by
  change (direction p, ‖(p : Plane)‖ - 1) = _
  simp

theorem radial_smul (p : Circle) {ρ : Real} (hρ : 0 < ρ) :
    radial (ρ • (p : Plane)) = (p, ρ - 1) := by
  change (direction (ρ • (p : Plane)), ‖ρ • (p : Plane)‖ - 1) = _
  simp [direction_smul p hρ, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]

end Poincare.Manifold.Schoenflies.CircleCollar

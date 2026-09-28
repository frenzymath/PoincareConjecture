import PoincareConjecture.Proofs.M76.Mathlib.CoreRadialCompression
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set

namespace Geometry

variable {ι : Type*}

def coordinateCylinder (J : Finset ι) : Set (ι → ℝ) :=
  {x | ∀ i ∈ J, |x i| ≤ 1}

theorem isClosed_coordinateCylinder (J : Finset ι) : IsClosed (coordinateCylinder J) := by
  have he : coordinateCylinder J = ⋂ i ∈ J, {x : ι → ℝ | |x i| ≤ 1} := by
    ext x
    simp [coordinateCylinder]
  rw [he]
  exact isClosed_biInter fun i _ => isClosed_le (continuous_apply i).abs continuous_const

theorem convex_coordinateCylinder (J : Finset ι) : Convex ℝ (coordinateCylinder J) := by
  have he : coordinateCylinder J = ⋂ i ∈ J, {x : ι → ℝ | |x i| ≤ 1} := by
    ext x
    simp [coordinateCylinder]
  rw [he]
  apply convex_iInter
  intro i
  apply convex_iInter
  intro _
  simpa only [preimage, mem_Icc, LinearMap.proj_apply, ← abs_le] using
    (convex_Icc (-1 : ℝ) 1).linear_preimage (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)

theorem smul_mem_coordinateCylinder (J : Finset ι) {x : ι → ℝ}
    (hx : x ∈ coordinateCylinder J) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ coordinateCylinder J := by
  intro i hi
  change |t * x i| ≤ 1
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_left (hx i hi) ht.1).trans (by simpa using ht.2)

theorem coreCompression_mem_coordinateCylinder [Fintype ι] (J : Finset ι) {x : ι → ℝ}
    (hx : x ∈ coordinateCylinder J) : NormedSpace.coreCompression x ∈ coordinateCylinder J := by
  apply smul_mem_coordinateCylinder J hx
  have hd : 0 < 1 + max 1 ‖x‖ := by positivity
  refine ⟨(div_pos (by norm_num) hd).le, (div_le_one hd).mpr ?_⟩
  have h := le_max_left (1 : ℝ) ‖x‖
  linarith

noncomputable def coordinateCylinderForms (J : Finset ι) : Finset ((ι → ℝ) →ᵃ[ℝ] ℝ) := by
  classical
  exact (J.image fun i => (LinearMap.proj i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 1) ∪
    (J.image fun i => -(LinearMap.proj i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 1)

theorem mem_coordinateCylinder_iff (J : Finset ι) (x : ι → ℝ) :
    x ∈ coordinateCylinder J ↔ ∀ A ∈ coordinateCylinderForms J, A x ≤ 0 := by
  classical
  constructor
  · intro hx A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      change x i - 1 ≤ 0
      exact sub_nonpos.mpr (abs_le.mp (hx i hi)).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      change -x i - 1 ≤ 0
      have h := (abs_le.mp (hx i hi)).1
      linarith
  · intro h i hi
    have hp := h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    have hn := h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    change x i - 1 ≤ 0 at hp
    change -x i - 1 ≤ 0 at hn
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Geometry

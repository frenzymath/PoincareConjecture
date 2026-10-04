import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreRadialCompression
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Closed coordinate cylinders for topological handles

Bounding selected coordinates by one models the closed base
of a handle. The cylinder is closed and convex and is retained
by contractions towards the origin. See Hamilton 1976,
pp. 64, 67--68 and M76 derivation 88.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {ι : Type*}

/-- The closed unit coordinate cylinder, with the coordinates
outside `J` unrestricted. See Hamilton p. 64 and M76 derivation 88. -/
def coordinateCylinder (J : Finset ι) : Set (ι → ℝ) :=
  {x | ∀ i ∈ J, |x i| ≤ 1}

/-- Coordinate cylinders are closed in the product topology.
See Hamilton p. 64 and M76 derivation 88. -/
theorem isClosed_coordinateCylinder (J : Finset ι) : IsClosed (coordinateCylinder J) := by
  have he : coordinateCylinder J = ⋂ i ∈ J, {x : ι → ℝ | |x i| ≤ 1} := by
    ext x
    simp [coordinateCylinder]
  rw [he]
  exact isClosed_biInter fun i _ => isClosed_le (continuous_apply i).abs continuous_const

/-- Coordinate cylinders are convex. See Hamilton p. 64 and
M76 derivation 88. -/
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

/-- Contracting by a scalar in the unit interval preserves the
coordinate cylinder. See M76 derivation 88. -/
theorem smul_mem_coordinateCylinder (J : Finset ι) {x : ι → ℝ}
    (hx : x ∈ coordinateCylinder J) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ coordinateCylinder J := by
  intro i hi
  change |t * x i| ≤ 1
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_left (hx i hi) ht.1).trans (by simpa using ht.2)

/-- Core radial compression sends each coordinate cylinder into
itself. See Hamilton pp. 67--68 and M76 derivation 88. -/
theorem coreCompression_mem_coordinateCylinder [Fintype ι] (J : Finset ι) {x : ι → ℝ}
    (hx : x ∈ coordinateCylinder J) : NormedSpace.coreCompression x ∈ coordinateCylinder J := by
  apply smul_mem_coordinateCylinder J hx
  have hd : 0 < 1 + max 1 ‖x‖ := by positivity
  refine ⟨(div_pos (by norm_num) hd).le, (div_le_one hd).mpr ?_⟩
  have h := le_max_left (1 : ℝ) ‖x‖
  linarith

/-- The finitely many affine inequalities defining a coordinate
cylinder. See Hamilton pp. 67--68 and M76 derivation 88. -/
noncomputable def coordinateCylinderForms (J : Finset ι) : Finset ((ι → ℝ) →ᵃ[ℝ] ℝ) := by
  classical
  exact (J.image fun i => (LinearMap.proj i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 1) ∪
    (J.image fun i => -(LinearMap.proj i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 1)

/-- Membership in the cylinder is exactly its finite affine
halfspace description. See M76 derivation 88. -/
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

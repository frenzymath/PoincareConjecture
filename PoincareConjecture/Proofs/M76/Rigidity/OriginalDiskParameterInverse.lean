import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskParameter
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem exists_disk_parameter_inverse :
    ∃ b : V2 → (T.index → ℝ × V3), FinitePiecewiseAffineOn b D ∧
      InjOn b D ∧ b '' D = (T.marked 2).space ∧
      (∀ z ∈ D, T.parameter (b z) = z) ∧
      (∀ z ∈ D, (T.inverse (b z) : X) = j z) ∧
      ∀ z ∈ D, b z ∈ (T.marked 1).space ↔ z ∈ Q := by
  classical
  have hu : FinitePiecewiseAffineOn T.parameter (T.marked 2).space :=
    ⟨T.marked 2, T.marked_finite 2, rfl,
      fun s hs => T.parameter_affine s (T.marked_le 2 hs)⟩
  obtain ⟨H0, _, hH0val⟩ := hu.exists_homeomorph_image T.disk_parameter_image.1
  let H : (T.marked 2).space ≃ₜ D :=
    H0.trans (Homeomorph.setCongr T.disk_parameter_image.2)
  have hHval (x : (T.marked 2).space) : (H x : V2) = T.parameter x := hH0val x
  have hH : H.IsFinitePL := ⟨T.parameter, hu, hHval⟩
  obtain ⟨b, hb, hvalue⟩ := hH.symm
  have hmem (z : V2) (hz : z ∈ D) : b z ∈ (T.marked 2).space := by
    rw [← hvalue ⟨z, hz⟩]
    exact (H.symm ⟨z, hz⟩).property
  have hparam (z : V2) (hz : z ∈ D) : T.parameter (b z) = z := by
    rw [← hvalue ⟨z, hz⟩, ← hHval (H.symm ⟨z, hz⟩), H.apply_symm_apply]
  refine ⟨b, hb, ?_, ?_, hparam, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (hparam x hx).symm.trans ((congrArg T.parameter hxy).trans (hparam y hy))
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmem z hz
    · intro hx
      refine ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, ?_⟩
      rw [← hvalue (H ⟨x, hx⟩), H.symm_apply_apply]
  · intro z hz
    have hj := (T.parameter_disk_point (hmem z hz)).2
    rw [hparam z hz] at hj
    exact hj.symm
  · intro z hz
    have hrim := T.parameter_mem_rim_iff (hmem z hz)
    rw [hparam z hz, ← T.disk_boundary_inter] at hrim
    exact (and_iff_right (hmem z hz)).symm.trans hrim.symm

end PoincareConjecture.M76.OriginalProperDiskTriangulation

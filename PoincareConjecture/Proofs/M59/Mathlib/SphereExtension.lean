import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension

set_option autoImplicit false

noncomputable section

open Metric Set

namespace PoincareConjecture.Proofs.M59

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def closedUnitBallRetraction : C(E, closedBall (0 : E) 1) where
  toFun z := ⟨(max 1 ‖z‖)⁻¹ • z, by
    have hpos : 0 < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hpos, ← div_eq_inv_mul]
    exact (div_le_one hpos).mpr (le_max_right _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.max continuous_norm).inv₀
      (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)))).smul continuous_id

theorem closedUnitBallRetraction_sphere (z : sphere (0 : E) 1) :
    closedUnitBallRetraction z.val = ⟨z.val, sphere_subset_closedBall z.property⟩ := by
  apply Subtype.ext
  simp [closedUnitBallRetraction, mem_sphere_zero_iff_norm.mp z.property]

theorem exists_extension_of_sphere_nullhomotopic [FiniteDimensional ℝ E] [Nontrivial E]
    {Y : Type*} [TopologicalSpace Y] (f : C(sphere (0 : E) 1, Y))
    (hf : f.Nullhomotopic) :
    ∃ F : C(E, Y), ∀ z : sphere (0 : E) 1, F z.val = f z := by
  obtain ⟨F, hF⟩ := M02.Topology.exists_disk_extension_of_nullhomotopic f hf
  refine ⟨F.comp closedUnitBallRetraction, ?_⟩
  intro z
  change F (closedUnitBallRetraction z.val) = f z
  rw [closedUnitBallRetraction_sphere]
  exact hF z

end PoincareConjecture.Proofs.M59

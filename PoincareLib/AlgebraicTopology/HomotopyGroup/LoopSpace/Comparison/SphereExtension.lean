import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# Whole-space extensions of null sphere maps

The closed unit ball is a retract of its ambient normed space. Composing
this retraction with the cone extension converts a sphere nullhomotopy to
the whole-plane filling used by MT's loop convention, pp. 429-430.
-/

set_option autoImplicit false

noncomputable section

open Metric Set

namespace PoincareMT.Proofs.M59

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial truncation onto the closed unit ball. Source: the cone filling
construction for MT Claim 18.16, p. 430; Hatcher Lemma 4.7, p. 348. -/
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

/-- Radial truncation fixes the sphere pointwise. Source: the filling
construction for MT Claim 18.16, p. 430. -/
theorem closedUnitBallRetraction_sphere (z : sphere (0 : E) 1) :
    closedUnitBallRetraction z.val = ⟨z.val, sphere_subset_closedBall z.property⟩ := by
  apply Subtype.ext
  simp [closedUnitBallRetraction, mem_sphere_zero_iff_norm.mp z.property]

/-- A nullhomotopic sphere map has a continuous extension to the whole ambient
space. Source: Hatcher Lemma 4.7, p. 348; MT Claim 18.16, p. 430. -/
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

end PoincareMT.Proofs.M59

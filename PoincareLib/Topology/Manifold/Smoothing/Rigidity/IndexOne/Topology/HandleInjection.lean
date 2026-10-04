import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLatticeHandleModel
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerPeriodLattice
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.RetractionFundamentalGroup
import Mathlib.Topology.Order.ProjIcc

/-!
# The actual interval-torus handle retracts from its ambient product

Clip the interval coordinate to its original closed unit ball and leave the
quotient-torus coordinate unchanged. The resulting continuous retraction
proves injectivity at every original handle basepoint. This is the literal
product model in Hamilton (1976), pp. 66--67.
-/

set_option autoImplicit false
open Set Metric

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L

/-- Coordinate clipping retracts onto the actual closed handle while fixing
the quotient-torus coordinate literally. -/
noncomputable def handleAmbientRetraction : C(X, R) := by
  let clip : ℝ → Icc (-1 : ℝ) 1 := projIcc (-1) 1 (by norm_num)
  have hclip : Continuous clip := continuous_projIcc
  have hmem (z : X) : ((fun i => (clip (z.1 i) : ℝ)), z.2) ∈ R := by
    refine ⟨?_, mem_univ _⟩
    have hn : ‖fun i => (clip (z.1 i) : ℝ)‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      exact Real.norm_eq_abs _ ▸ abs_le.mpr (clip (z.1 i)).property
    simpa only [mem_closedBall, dist_zero_right] using hn
  exact ⟨fun z => ⟨((fun i => (clip (z.1 i) : ℝ)), z.2), hmem z⟩,
    ((continuous_pi fun i => continuous_subtype_val.comp
      (hclip.comp ((continuous_apply i).comp continuous_fst))).prodMk
        continuous_snd).subtype_mk _⟩

/-- The retraction fixes every point of the literal closed handle. -/
theorem handleAmbientRetraction_apply_coe (x : R) :
    handleAmbientRetraction (x : X) = x := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hn : ‖x.val.1‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property.1
    have hi : x.val.1 i ∈ Icc (-1 : ℝ) 1 := by
      have hi := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hn i
      exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hi)
    change (projIcc (-1) 1 (by norm_num) (x.val.1 i) : ℝ) = x.val.1 i
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hi)
  · rfl

/-- Inclusion of the complete closed handle into its original ambient product
induces an injection at every handle basepoint. -/
theorem handle_ambient_pi1_injective (x : R) :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)) x) :=
  FundamentalGroup.map_injective_of_leftInverse
    (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)) handleAmbientRetraction
    handleAmbientRetraction_apply_coe x

end PoincareMT.M76.HamiltonIntervalTorus

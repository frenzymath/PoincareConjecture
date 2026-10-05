import PoincareLib.Topology.Manifold.Smoothing.Dehn.Loops.Mathlib.OldResolutionEndPaths
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Loops.Mathlib.OriginalStripEndPaths
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Mathlib.TubeArmOrientation

/-!
# The original strip ends are the reoriented old diagonals

The exact affine parameter is retained across the source strip, the original
sheet formula, and the marked diagonal constructed in the endpoint square.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

/-- The selected orientation sends both entire new diagonals to the
original outer-to-middle sheet parameters, with the same parameter value. -/
theorem tubeArmOrientation_old_diagonals (s0 s1 : Bool) (t : ℝ) (s : unitInterval) :
    tubeArmOrientation s0 s1 ((-1 + 2 * (s : ℝ), 1 - 2 * (s : ℝ)), t) =
      ((originalStripEndParameter s0 s, originalStripEndParameter s0 s), t) ∧
    tubeArmOrientation s0 s1 ((1 - 2 * (s : ℝ), 1 - 2 * (s : ℝ)), t) =
      ((originalStripEndParameter s1 s, -originalStripEndParameter s1 s), t) := by
  cases s0 <;> cases s1 <;> constructor <;>
    ext <;> simp [tubeArmOrientation, originalStripEndParameter, farArmParameter] <;> ring

/-- The original two sheet equations identify both full strip-end paths
with the actual reoriented diagonals in the target. -/
theorem reoriented_tube_old_end_equations
    {E X : Type*} [TopologicalSpace E]
    (f : E → X) (c0 c1 : P2 → E) (τ : C3 → X)
    (hc0 : ContinuousOn c0 source) (hc1 : ContinuousOn c1 source)
    (h0 : ∀ p ∈ source, f (c0 p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c1 p) = τ ((p.2, -p.2), p.1))
    (s0 s1 : Bool) (t s : unitInterval) :
    f (originalStripEndPath c0 hc0 t s0 s) =
      (τ ∘ tubeArmOrientation s0 s1) ((-1 + 2 * (s : ℝ), 1 - 2 * (s : ℝ)), (t : ℝ)) ∧
    f (originalStripEndPath c1 hc1 t s1 s) =
      (τ ∘ tubeArmOrientation s0 s1) ((1 - 2 * (s : ℝ), 1 - 2 * (s : ℝ)), (t : ℝ)) := by
  obtain ⟨hAR, hCL⟩ := tubeArmOrientation_old_diagonals s0 s1 (t : ℝ) s
  dsimp only [Function.comp_apply]
  rw [hAR, hCL, originalStripEndPath_val, originalStripEndPath_val]
  exact ⟨h0 _ ⟨t.property, originalStripEndParameter_mem s0 s⟩,
    h1 _ ⟨t.property, originalStripEndParameter_mem s1 s⟩⟩

/-- The marked old diagonal data evaluates to the original source strip
paths after the original map, at every parameter including both endpoints. -/
theorem marked_old_end_data_original_strip_values
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {Fmark : Set X}
    (f : E → X) (c0 c1 : P2 → E) (τ : C3 → X)
    (hc0 : ContinuousOn c0 source) (hc1 : ContinuousOn c1 source)
    (h0 : ∀ p ∈ source, f (c0 p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c1 p) = τ ((p.2, -p.2), p.1))
    (s0 s1 : Bool) {b : ℝ} (t : unitInterval)
    (d : MarkedResolutionEndData Fmark (τ ∘ tubeArmOrientation s0 s1) b t)
    (D : MarkedResolutionOldEndData d) (s : unitInterval) :
    (D.AR s : X) = f (originalStripEndPath c0 hc0 t s0 s) ∧
      (D.CL s : X) = f (originalStripEndPath c1 hc1 t s1 s) := by
  obtain ⟨hAR, hCL⟩ := reoriented_tube_old_end_equations f c0 c1 τ hc0 hc1 h0 h1 s0 s1 t s
  exact ⟨(D.AR_val s).trans hAR.symm, (D.CL_val s).trans hCL.symm⟩

end PoincareMT.M76.Dehn.PolygonalCrossingResolution

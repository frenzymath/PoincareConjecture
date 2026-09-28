import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionStripBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)


def stripSourceCorner (t : unitInterval) (positive : Bool) : source :=
  ⟨((t : ℝ), if positive then 1 else -1), t.property, by cases positive <;> norm_num⟩


def stripSourceEndPath (t : unitInterval) :
    Path (stripSourceCorner t false) (stripSourceCorner t true) where
  toFun s := ⟨((t : ℝ), 2 * (s : ℝ) - 1), t.property, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [stripSourceCorner]
  target' := by apply Subtype.ext; norm_num [stripSourceCorner]

theorem stripSourceEndPath_val (t s : unitInterval) :
    (stripSourceEndPath t s : P2) = ((t : ℝ), 2 * (s : ℝ) - 1) := rfl


theorem stripSourceEndPath_mem_ends (t : unitInterval)
    (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) (s : unitInterval) :
    (stripSourceEndPath t s : P2) ∈ stripEnds := by
  refine ⟨?_, (stripSourceEndPath t s).property.2⟩
  simpa only [stripSourceEndPath_val, mem_insert_iff, mem_singleton_iff] using ht


theorem stripSourceEndPath_maps_to_mark
    {X : Type*} {Z : Set X} (τ : C3 → X)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Z)
    {b : ℝ} (hb : b ≤ 1) (alternatePair positive : Bool)
    (t : unitInterval) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) (s : unitInterval) :
    τ (resolutionMap b alternatePair positive (stripSourceEndPath t s)) ∈ Z :=
  resolution_strip_ends_in_mark τ hτmark hb alternatePair positive
    (stripSourceEndPath_mem_ends t ht s)



theorem stripSourceEndPath_upper_value
    {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : C3 → X}
    {b : ℝ} {t : unitInterval} (d : MarkedResolutionEndData Z τ b t) (s : unitInterval) :
    τ (strip b true (stripSourceEndPath t s)) = (d.U s : X) := (d.U_val s).symm

theorem stripSourceEndPath_left_value
    {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : C3 → X}
    {b : ℝ} {t : unitInterval} (d : MarkedResolutionEndData Z τ b t) (s : unitInterval) :
    τ (alternate b false (stripSourceEndPath t s)) = (d.L s : X) := (d.L_val s).symm

theorem stripSourceEndPath_right_value
    {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : C3 → X}
    {b : ℝ} {t : unitInterval} (d : MarkedResolutionEndData Z τ b t) (s : unitInterval) :
    τ (alternate b true (stripSourceEndPath t s)) = (d.R s : X) := (d.R_val s).symm

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

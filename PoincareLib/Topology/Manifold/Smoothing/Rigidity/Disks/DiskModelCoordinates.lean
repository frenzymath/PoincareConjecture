import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.IntrinsicDiskModel

/-!
# Literal original parameters on the marked disk image

The graph map, its actual model inverse and the retained disk
parameter identify every point of the whole marked disk. This
selects the same original pair-chart family for finite stars.
See Hudson pp. 12--19 and rigidity014, sections1--2.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

/-- Every point of the marked graph disk has its original disk
parameter, and that parameter gives exactly the literal original
model inverse. See rigidity014, sections1--2. -/
theorem disk_parameter_eq_model_inverse
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {C : Set X} {K : Set E} (H : C ≃ₜ K) (F : X → E) (g : E → C)
    (hHF : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K, (g z : X) = (H.symm z : X))
    {j : V2 → X} (hDC : MapsTo j D C) (u : E → V2)
    (hu : ∀ z : D, u (F (j z)) = (z : V2))
    {x : E} (hx : x ∈ F '' (j '' D)) :
    u x ∈ D ∧ j (u x) = (g x : X) := by
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  have huz : u (F (j z)) = z := hu ⟨z, hz⟩
  refine ⟨huz.symm ▸ hz, ?_⟩
  rw [huz]
  let zC : C := ⟨j z, hDC hz⟩
  have h := hg (H zC)
  rw [H.symm_apply_apply, hHF] at h
  exact h.symm

end PoincareMT.M76

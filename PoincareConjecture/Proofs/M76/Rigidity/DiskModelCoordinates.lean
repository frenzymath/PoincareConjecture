import PoincareConjecture.Proofs.M76.Rigidity.IntrinsicDiskModel

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

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

end PoincareConjecture.M76

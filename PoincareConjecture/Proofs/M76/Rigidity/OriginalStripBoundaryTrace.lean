import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem frontier_inter_openStrip (P : OriginalDiskProduct e R j) :
    frontier R ∩ P.openStrip =
      P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  have hfull : D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  ext y
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    exact ⟨z, ⟨(P.proper z (hfull hz)).mp hy, hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzD : z ∈ D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨sphere_subset_closedBall hz.1, hz.2⟩
    exact ⟨(P.proper z (hfull hzD)).mpr hz.1, z, hzD, rfl⟩

end PoincareConjecture.M76.OriginalDiskProduct

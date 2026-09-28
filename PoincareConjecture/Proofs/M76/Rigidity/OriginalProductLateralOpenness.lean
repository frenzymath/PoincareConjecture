import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.isOpen_lateral_image (P : OriginalDiskProduct e R j)
    (hR : IsClosed R) {ε : ℝ} (hε : ε ≤ 1)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε)))) :
    IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  let v : frontier R → R := Set.inclusion hR.frontier_subset
  have hv : Continuous v := continuous_subtype_val.subtype_mk _
  have heq : v ⁻¹' ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) =
      (Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-ε) ε)) := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzI : z.2 ∈ Icc (-1 : ℝ) 1 :=
        ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
      have hzQ : z.1 ∈ Q := (P.proper z ⟨hz.1, hzI⟩).mp (hzy.symm ▸ y.property)
      exact ⟨z, ⟨hzQ, hz.2⟩, hzy⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, ⟨sphere_subset_closedBall hz.1, hz.2⟩, hzy⟩
  exact heq ▸ hopen.preimage hv

end PoincareConjecture.M76

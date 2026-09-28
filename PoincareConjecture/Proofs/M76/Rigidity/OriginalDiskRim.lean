import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskModelFacts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)



theorem rim_parameter_image :
    InjOn T.parameter (T.marked 3).space ∧ T.parameter '' (T.marked 3).space = Q := by
  rw [T.rim_space]
  have hu (z : V2) (hz : z ∈ Q) : T.parameter (T.graph (j z)) = z :=
    T.parameter_original ⟨z, sphere_subset_closedBall hz⟩
  constructor
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩ h
    have hzv : z = v := (hu z hz).symm.trans (h.trans (hu v hv))
    exact congrArg (fun x => T.graph (j x)) hzv
  · apply Subset.antisymm
    · rintro _ ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      rw [hu z hz]
      exact hz
    · intro z hz
      exact ⟨T.graph (j z), ⟨j z, ⟨z, hz, rfl⟩, rfl⟩, hu z hz⟩



theorem rim_face_card_le {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 3).faces) : s.card ≤ 2 := by
  have hf : (T.marked 3).AffineOnFaces T.parameter :=
    fun t ht => T.parameter_affine t (T.marked_le 3 ht)
  obtain ⟨hi, himage⟩ := T.rim_parameter_image
  have hint : interior (T.parameter '' (T.marked 3).space) = ∅ := by
    rw [himage, interior_sphere']
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    hf.face_card_le_of_injOn_of_empty_interior hi hint hs

end PoincareConjecture.M76.OriginalProperDiskTriangulation

import Mathlib.Topology.Homeomorph.Lemmas









set_option autoImplicit false

open Set

namespace Topology.IsEmbedding

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [Zero E]




theorem exists_inverse_on_image {f : E → X} {S : Set E}
    (hf : IsEmbedding (fun z : S => f z)) :
    ∃ k : X → E, ContinuousOn k (f '' S) ∧
      (∀ z ∈ S, k (f z) = z) ∧
      (∀ y ∈ f '' S, f (k y) = y) ∧ MapsTo k (f '' S) S := by
  classical
  let H := hf.toHomeomorph
  let k : X → E := fun y => if hy : y ∈ range (fun z : S => f z) then
    (H.symm ⟨y, hy⟩ : E) else 0
  have hvalue (y : range (fun z : S => f z)) : k y = (H.symm y : E) := by
    simp only [k, dif_pos y.property]
  have himage : range (fun z : S => f z) = f '' S := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hleft (z : E) (hz : z ∈ S) : k (f z) = z := by
    have h := hvalue (H ⟨z, hz⟩)
    rw [H.symm_apply_apply] at h
    exact h
  refine ⟨k, ?_, hleft, ?_, ?_⟩
  · rw [← himage]
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp H.symm.continuous).congr (fun y => (hvalue y).symm)
  · rintro y ⟨z, hz, rfl⟩
    rw [hleft z hz]
  · rintro y ⟨z, hz, rfl⟩
    rwa [hleft z hz]

end Topology.IsEmbedding

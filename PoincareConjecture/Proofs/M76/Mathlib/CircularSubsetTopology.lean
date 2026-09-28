import PoincareConjecture.Proofs.M76.Mathlib.PuncturedCircle









set_option autoImplicit false

open Set

namespace Set




theorem isConnected_sdiff_singleton_of_homeomorph_circle {X : Type*}
    [TopologicalSpace X] (s : Set X) (e : s ≃ₜ Circle) (q : X) :
    IsConnected (s \ {q}) := by
  classical
  by_cases hq : q ∈ s
  · let x : s := ⟨q, hq⟩
    have hc := (Circle.isConnected_compl_singleton (e x)).image e.symm
      e.symm.continuous.continuousOn
    rw [e.symm.image_compl, image_singleton, e.symm_apply_apply] at hc
    have h := hc.image ((↑) : s → X) continuous_subtype_val.continuousOn
    rw [image_compl_eq_range_sdiff_image Subtype.val_injective,
      Subtype.range_coe, image_singleton] at h
    exact h
  · rw [sdiff_singleton_eq_self hq]
    let : ConnectedSpace s := e.connectedSpace_iff.mpr inferInstance
    simpa only [image_univ, Subtype.range_coe] using
      (isConnected_univ : IsConnected (univ : Set s)).image
        ((↑) : s → X) continuous_subtype_val.continuousOn

end Set

import Mathlib.Topology.OpenPartialHomeomorph.Constructions










set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X]




theorem exists_fill_fixed_core_on_open (e : OpenPartialHomeomorph X X)
    {U A C T : Set X} (hU : IsOpen U)
    (hsource : e.source = U \ A) (htarget : e.target = T \ A)
    (hC : IsClosed C) (hAC : A ⊆ interior C) (hCU : C ⊆ U) (hCT : C ⊆ T)
    (hfix : EqOn e id (C \ A)) :
    ∃ H : OpenPartialHomeomorph X X, H.source = U ∧ H.target = T ∧
      EqOn H id C ∧ EqOn H e Cᶜ := by
  classical
  have hCA : ∀ x ∈ frontier C, x ∉ A := by
    intro x hx hxA
    exact hx.2 (hAC hxA)
  have himage : e.IsImage C C := by
    intro x hx
    have hxA : x ∉ A := (hsource ▸ hx).2
    constructor
    · intro hexC
      have hexA : e x ∉ A := (htarget ▸ e.map_source hx).2
      have hexs : e x ∈ e.source := hsource.symm ▸ ⟨hCU hexC, hexA⟩
      have hexx : e (e x) = e x := hfix ⟨hexC, hexA⟩
      have hxex : x = e x := e.injOn hx hexs hexx.symm
      exact hxex.symm ▸ hexC
    · intro hxC
      simpa only [hfix ⟨hxC, hxA⟩, id_eq] using hxC
  have hfront : (ofSet U hU).source ∩ frontier C = e.source ∩ frontier C := by
    change U ∩ frontier C = e.source ∩ frontier C
    rw [hsource]
    ext x
    exact ⟨fun hx => ⟨⟨hx.1, hCA x hx.2⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
  have hfrontfix : EqOn (ofSet U hU) e ((ofSet U hU).source ∩ frontier C) := by
    intro x hx
    exact (hfix ⟨hC.frontier_subset hx.2, hCA x hx.2⟩).symm
  let H := (ofSet U hU).piecewise e C C
    (fun _ _ => Iff.rfl) himage hfront hfrontfix
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · change C.ite U e.source = U
    rw [hsource]
    ext x
    by_cases hx : x ∈ C
    · simp [Set.ite, hx]
    · have hxA : x ∉ A := fun h => hx (interior_subset (hAC h))
      simp [Set.ite, hx, hxA]
  · change C.ite U e.target = T
    rw [htarget]
    ext x
    by_cases hx : x ∈ C
    · simp [Set.ite, hx, hCU hx, hCT hx]
    · have hxA : x ∉ A := fun h => hx (interior_subset (hAC h))
      simp [Set.ite, hx, hxA]
  · intro x hx
    change C.piecewise (ofSet U hU) e x = x
    rw [piecewise_eq_of_mem C _ _ hx]
    rfl
  · intro x hx
    change C.piecewise (ofSet U hU) e x = e x
    exact piecewise_eq_of_notMem C _ _ hx

end OpenPartialHomeomorph

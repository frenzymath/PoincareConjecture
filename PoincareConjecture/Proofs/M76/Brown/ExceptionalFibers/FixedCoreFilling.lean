import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X]

theorem exists_fill_fixed_core (e : OpenPartialHomeomorph X X)
    {A C T : Set X} (hsource : e.source = Aᶜ) (htarget : e.target = T \ A)
    (hC : IsClosed C) (hAC : A ⊆ interior C) (hCT : C ⊆ T)
    (hfix : EqOn e id (C \ A)) :
    ∃ H : OpenPartialHomeomorph X X, H.source = univ ∧ H.target = T ∧
      EqOn H id C ∧ EqOn H e Cᶜ := by
  classical
  have hCA : ∀ x ∈ frontier C, x ∉ A := by
    intro x hx hxA
    exact hx.2 (hAC hxA)
  have himage : e.IsImage C C := by
    intro x hx
    have hxA : x ∈ Aᶜ := by simpa only [hsource] using hx
    constructor
    · intro hexC
      have hexA : e x ∉ A := (htarget ▸ e.map_source hx).2
      have hexx : e (e x) = e x := hfix ⟨hexC, hexA⟩
      have hxex : x = e x := e.injOn hx (hsource.symm ▸ hexA) hexx.symm
      exact hxex.symm ▸ hexC
    · intro hxC
      simpa only [hfix ⟨hxC, hxA⟩, id_eq] using hxC
  have hfront : (OpenPartialHomeomorph.refl X).source ∩ frontier C =
      e.source ∩ frontier C := by
    change univ ∩ frontier C = e.source ∩ frontier C
    rw [univ_inter, hsource]
    ext x
    exact ⟨fun hx => ⟨hCA x hx, hx⟩, fun hx => hx.2⟩
  have hfrontfix : EqOn (OpenPartialHomeomorph.refl X) e
      ((OpenPartialHomeomorph.refl X).source ∩ frontier C) := by
    intro x hx
    exact (hfix ⟨hC.frontier_subset hx.2, hCA x hx.2⟩).symm
  let H := (OpenPartialHomeomorph.refl X).piecewise e C C
    (fun _ _ => Iff.rfl) himage hfront hfrontfix
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · change C.ite univ e.source = univ
    rw [hsource]
    ext x
    by_cases hx : x ∈ C
    · simp [Set.ite, hx]
    · have hxA : x ∉ A := fun h => hx (interior_subset (hAC h))
      simp [Set.ite, hx, hxA]
  · change C.ite univ e.target = T
    rw [htarget]
    ext x
    by_cases hx : x ∈ C
    · simp [Set.ite, hx, hCT hx]
    · have hxA : x ∉ A := fun h => hx (interior_subset (hAC h))
      simp [Set.ite, hx, hxA]
  · intro x hx
    change C.piecewise (OpenPartialHomeomorph.refl X) e x = x
    simp only [piecewise_eq_of_mem C _ _ hx, refl_apply, id_eq]
  · intro x hx
    change C.piecewise (OpenPartialHomeomorph.refl X) e x = e x
    exact piecewise_eq_of_notMem C _ _ hx

variable {Y : Type*} [TopologicalSpace Y] [RegularSpace Y]

theorem exists_closed_fiber_core {q : X → Y} (hq : Continuous q)
    (c : Y) {V : Set Y} (hV : IsOpen V) (hc : c ∈ V) :
    ∃ C : Set X, IsClosed C ∧ q ⁻¹' {c} ⊆ interior C ∧ C ⊆ q ⁻¹' V := by
  obtain ⟨D, hDn, hD, hDV⟩ := exists_mem_nhds_isClosed_subset (hV.mem_nhds hc)
  refine ⟨q ⁻¹' D, hD.preimage hq, ?_, preimage_mono hDV⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  apply hq.continuousAt.preimage_mem_nhds
  change q x = c at hx
  rw [hx]
  exact hDn

end OpenPartialHomeomorph

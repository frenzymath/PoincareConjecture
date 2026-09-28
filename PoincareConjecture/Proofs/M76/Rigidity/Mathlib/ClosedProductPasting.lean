import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn









set_option autoImplicit false

open Set

namespace ContinuousMap

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X]
  [TopologicalSpace Y]




theorem exists_paste_of_eq_on_frontier {C : Set X} (hC : IsClosed C)
    (G : C(T × C, Y)) (H : C(T × X, Y))
    (hfront : ∀ (t : T) (x : C), (x : X) ∈ frontier C → G (t, x) = H (t, x)) :
    ∃ F : C(T × X, Y),
      (∀ (t : T) (x : C), F (t, x) = G (t, x)) ∧
      ∀ (t : T) (x : X), x ∉ interior C → F (t, x) = H (t, x) := by
  classical
  let f : T × X → Y := fun z =>
    if hx : z.2 ∈ C then G (z.1, ⟨z.2, hx⟩) else H z
  have hfC (t : T) (x : X) (hx : x ∈ C) :
      f (t, x) = G (t, ⟨x, hx⟩) := dif_pos hx
  have hfout (t : T) (x : X) (hx : x ∉ interior C) : f (t, x) = H (t, x) := by
    by_cases hxC : x ∈ C
    · rw [hfC t x hxC]
      apply hfront
      rw [frontier, hC.closure_eq]
      exact ⟨hxC, hx⟩
    · exact dif_neg hxC
  let A : Set (T × X) := Prod.snd ⁻¹' C
  let B : Set (T × X) := Prod.snd ⁻¹' (interior C)ᶜ
  have hfA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : A → T × C := fun z => (z.1.1, ⟨z.1.2, z.2⟩)
    have hk : Continuous k := continuous_subtype_val.fst.prodMk
      (continuous_subtype_val.snd.subtype_mk _)
    convert G.continuous.comp hk using 1
    ext z
    exact hfC z.1.1 z.1.2 z.2
  have hfB : ContinuousOn f B :=
    H.continuous.continuousOn.congr (fun z hz => hfout z.1 z.2 hz)
  have hcover : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z.2 ∈ C
    · exact Or.inl hz
    · exact Or.inr (fun h => hz (interior_subset h))
  have hfc : Continuous f := by
    have h := hfA.union_of_isClosed hfB (hC.preimage continuous_snd)
      (isOpen_interior.isClosed_compl.preimage continuous_snd)
    rw [hcover] at h
    exact continuousOn_univ.mp h
  exact ⟨⟨f, hfc⟩, fun t x => hfC t x x.property, hfout⟩

end ContinuousMap

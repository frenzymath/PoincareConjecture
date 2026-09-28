import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

open Set unitInterval

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X] {R C : Set X} {V : Set C}

theorem exists_interior_homotopy_pasting
    (hC : IsClosed C) (hCR : C ⊆ interior R)
    (G : C(I × C, X)) (hGR : ∀ z, G z ∈ interior R)
    (hG0 : ∀ x : C, G (0, x) = (x : X))
    (hV : IsOpen V) (hfront : (Subtype.val : C → X) ⁻¹' frontier C ⊆ V)
    (hfix : ∀ (t : I) (x : C), x ∈ V → G (t, x) = (x : X)) :
    ∃ (T : C(I × R, R)) (W : Set X),
      IsOpen W ∧ (interior C)ᶜ ⊆ W ∧
      (∀ (t : I) (x : C),
        (T (t, ⟨x, interior_subset (hCR x.property)⟩) : X) = G (t, x)) ∧
      (∀ (t : I) (x : R), (x : X) ∈ W → T (t, x) = x) ∧
      (∀ x : R, T (0, x) = x) ∧
      ∀ t : I,
        (fun x : R => T (t, x)) ⁻¹' ((Subtype.val : R → X) ⁻¹' frontier R) =
          (Subtype.val : R → X) ⁻¹' frontier R := by
  classical
  let f : I × R → X := fun z =>
    if hx : (z.2 : X) ∈ C then G (z.1, ⟨z.2, hx⟩) else z.2
  have hfC (t : I) (x : R) (hx : (x : X) ∈ C) :
      f (t, x) = G (t, ⟨x, hx⟩) := dif_pos hx
  have hfout (t : I) (x : R) (hx : (x : X) ∉ interior C) : f (t, x) = x := by
    by_cases hxC : (x : X) ∈ C
    · rw [hfC t x hxC]
      apply hfix
      apply hfront
      rw [frontier, hC.closure_eq]
      exact ⟨hxC, hx⟩
    · exact dif_neg hxC
  let A : Set (I × R) := (fun z => (z.2 : X)) ⁻¹' C
  let B : Set (I × R) := (fun z => (z.2 : X)) ⁻¹' (interior C)ᶜ
  have hfA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : A → I × C := fun z => (z.1.1, ⟨z.1.2, z.2⟩)
    have hk : Continuous k := continuous_subtype_val.fst.prodMk
      ((continuous_subtype_val.comp continuous_subtype_val.snd).subtype_mk _)
    convert G.continuous.comp hk using 1
    ext z
    exact hfC z.1.1 z.1.2 z.2
  have hfB : ContinuousOn f B :=
    (continuous_subtype_val.comp continuous_snd).continuousOn.congr
      (fun z hz => hfout z.1 z.2 hz)
  have hcover : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : (z.2 : X) ∈ C
    · exact Or.inl hz
    · exact Or.inr (fun h => hz (interior_subset h))
  have hfc : Continuous f := by
    have h := hfA.union_of_isClosed hfB
      (hC.preimage (continuous_subtype_val.comp continuous_snd))
      (isOpen_interior.isClosed_compl.preimage (continuous_subtype_val.comp continuous_snd))
    rw [hcover] at h
    exact continuousOn_univ.mp h
  have hfR (z : I × R) : f z ∈ R := by
    by_cases hx : (z.2 : X) ∈ C
    · rw [show f z = G (z.1, ⟨z.2, hx⟩) from hfC z.1 z.2 hx]
      exact interior_subset (hGR _)
    · simpa only [f, dif_neg hx] using z.2.property
  let T : C(I × R, R) := ⟨fun z => ⟨f z, hfR z⟩, hfc.subtype_mk _⟩
  obtain ⟨O, hO, hVO⟩ := isOpen_induced_iff.mp hV
  refine ⟨T, O ∪ Cᶜ, hO.union hC.isOpen_compl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxC : x ∈ C
    · left
      have hxV : (⟨x, hxC⟩ : C) ∈ V := hfront (by
        rw [frontier, hC.closure_eq]
        exact ⟨hxC, hx⟩)
      rwa [← hVO] at hxV
    · exact Or.inr hxC
  · intro t x
    exact hfC t ⟨x, interior_subset (hCR x.property)⟩ x.property
  · intro t x hx
    apply Subtype.ext
    change f (t, x) = (x : X)
    by_cases hxC : (x : X) ∈ C
    · rw [hfC t x hxC]
      apply hfix
      rw [← hVO]
      exact hx.resolve_right (fun h => h hxC)
    · exact dif_neg hxC
  · intro x
    apply Subtype.ext
    change f (0, x) = (x : X)
    by_cases hxC : (x : X) ∈ C
    · rw [hfC 0 x hxC, hG0]
    · exact dif_neg hxC
  · intro t
    ext x
    change f (t, x) ∈ frontier R ↔ (x : X) ∈ frontier R
    by_cases hxC : (x : X) ∈ C
    · rw [hfC t x hxC]
      exact iff_of_false (fun h => h.2 (hGR _)) (fun h => h.2 (hCR hxC))
    · rw [show f (t, x) = (x : X) from dif_neg hxC]

end PoincareConjecture.M76

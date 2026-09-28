import Mathlib.Topology.Piecewise
import Mathlib.Topology.Constructions

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X]

theorem exists_relative_core_retraction {K N U S : Set X}
    (hN : IsClosed N) (hNK : N ⊆ K) (hUN : U ⊆ N)
    (hopen : IsOpen ((Subtype.val : K → X) ⁻¹' U)) (hlevel : N \ U = S)
    (r0 : X → X) (hr0 : ContinuousOn r0 N) (hmap : MapsTo r0 N S)
    (hfix : EqOn r0 id S) :
    ∃ r : K → X, Continuous r ∧ range r = K \ U ∧
      ∀ x : K, (x : X) ∈ K \ U → r x = x := by
  classical
  let r : K → X := fun x => if (x : X) ∈ N then r0 x else x
  have hNpre : IsClosed ((Subtype.val : K → X) ⁻¹' N) :=
    hN.preimage continuous_subtype_val
  have hcont : Continuous r := by
    apply continuous_if
    · intro x hx
      have hxN : (x : X) ∈ N := hNpre.frontier_subset hx
      have hxU : (x : X) ∉ U := by
        intro hxU
        exact hx.2 (interior_maximal (preimage_mono hUN) hopen hxU)
      exact hfix (hlevel.subset ⟨hxN, hxU⟩)
    · change ContinuousOn (r0 ∘ (Subtype.val : K → X))
        (closure ((Subtype.val : K → X) ⁻¹' N))
      rw [hNpre.closure_eq]
      exact hr0.comp continuous_subtype_val.continuousOn (fun _ hx => hx)
    · exact continuous_subtype_val.continuousOn
  have hmaps (x : K) : r x ∈ K \ U := by
    dsimp [r]
    split_ifs with hxN
    · have h := hlevel.symm.subset (hmap hxN)
      exact ⟨hNK h.1, h.2⟩
    · exact ⟨x.property, fun hxU => hxN (hUN hxU)⟩
  have hidentity (x : K) (hx : (x : X) ∈ K \ U) : r x = x := by
    dsimp [r]
    split_ifs with hxN
    · exact hfix (hlevel.subset ⟨hxN, hx.2⟩)
    · rfl
  refine ⟨r, hcont, ?_, hidentity⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact hmaps y
  · intro hx
    exact ⟨⟨x, hx.1⟩, hidentity ⟨x, hx.1⟩ hx⟩

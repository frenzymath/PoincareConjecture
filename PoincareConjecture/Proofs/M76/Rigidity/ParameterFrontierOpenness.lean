import PoincareConjecture.Proofs.M76.Rigidity.ParameterPrismDomain

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem isOpen_parameterPrism_frontier_of_lateral {A : Set E}
    (hA : A ⊆ Q ×ˢ Ioo (-1 : ℝ) 1)
    (hopen : IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹' A)) :
    IsOpen ((Subtype.val : frontier (D ×ˢ I) → E) ⁻¹' A) := by
  let f : Q × ℝ → E := fun z => ((z.1 : V2), z.2)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.prodMap (Homeomorph.refl ℝ).isEmbedding
  obtain ⟨O, hO, hOp⟩ := hf.isInducing.isOpen_iff.mp hopen
  have hiff (z : E) (hz : z.1 ∈ Q) : z ∈ O ↔ z ∈ A := by
    have h := Set.ext_iff.mp hOp (⟨z.1, hz⟩, z.2)
    exact h
  have heq : (Subtype.val : frontier (D ×ˢ I) → E) ⁻¹' A =
      (Subtype.val : frontier (D ×ˢ I) → E) ⁻¹' O ∩
        (fun z : frontier (D ×ˢ I) => (z : E).2) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext z
    constructor
    · intro hz
      exact ⟨(hiff z (hA hz).1).mpr hz, (hA hz).2⟩
    · rintro ⟨hzO, hzt⟩
      have hzQ : (z : E).1 ∈ Q := by
        have hfront := originalParameterPrism_frontier.subset z.property
        rcases hfront with h | h
        · exact h.1
        · have ht : (z : E).2 = -1 ∨ (z : E).2 = 1 := h.2
          rcases ht with h | h <;> linarith [hzt.1, hzt.2]
      exact (hiff z hzQ).mp hzO
  rw [heq]
  exact (hO.preimage continuous_subtype_val).inter
    (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))

end PoincareConjecture.M76

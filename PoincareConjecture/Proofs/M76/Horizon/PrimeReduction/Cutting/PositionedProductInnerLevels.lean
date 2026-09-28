import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import Mathlib.Topology.UnitInterval








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_positioned_product_inner_levels
    {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [CompactSpace D]
    (p : D × unitInterval → X) (hp : Continuous p) {F : Set X} (hF : IsClosed F)
    (hends : ∀ z, (z.2 = 0 ∨ z.2 = 1) → p z ∉ F) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
      (∀ z, p z ∈ F → δ < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1-δ) ∧
      ∀ z, ((z.2 : ℝ) = δ ∨ (z.2 : ℝ) = 1-δ) → p z ∉ F := by
  let bad := p ⁻¹' F
  have hbad : IsCompact bad := (hF.preimage hp).isCompact
  have hpos (z : D × unitInterval) (hz : z ∈ bad) : 0 < (z.2 : ℝ) := by
    apply lt_of_le_of_ne z.2.property.1
    intro heq
    exact hends z (Or.inl (Subtype.ext heq.symm)) hz
  have hlt (z : D × unitInterval) (hz : z ∈ bad) : (z.2 : ℝ) < 1 := by
    apply lt_of_le_of_ne z.2.property.2
    intro heq
    exact hends z (Or.inr (Subtype.ext heq)) hz
  have hlow : ∃ a : ℝ, 0 < a ∧ ∀ z ∈ bad, a ≤ (z.2 : ℝ) :=
    hbad.exists_forall_le' (continuous_subtype_val.comp continuous_snd).continuousOn hpos
  have hhigh : ∃ b : ℝ, b < 1 ∧ ∀ z ∈ bad, (z.2 : ℝ) ≤ b :=
    hbad.exists_forall_le' (α := OrderDual ℝ)
      (show ContinuousOn (fun z : D × unitInterval => (z.2 : ℝ)) bad from
        (continuous_subtype_val.comp continuous_snd).continuousOn) hlt
  obtain ⟨a,ha,haall⟩ := hlow
  obtain ⟨b,hb,hball⟩ := hhigh
  let δ := min (1/4 : ℝ) (min (a/2) ((1-b)/2))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδa : δ ≤ a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (1-b)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hmiddle (z : D × unitInterval) (hz : p z ∈ F) :
      δ < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1-δ := by
    have hzlo := haall z hz
    have hzhi := hball z hz
    constructor <;> linarith
  refine ⟨δ,hδ,min_le_left _ _,hmiddle,?_⟩
  intro z hz hzF
  have hm := hmiddle z hzF
  rcases hz with hz | hz <;> linarith [hm.1,hm.2]

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarFrontier
import Mathlib.Topology.UnitInterval








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_closed_collar_product
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {A : Set E} (hA : IsCompact A) (c : E × ℝ → X)
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (A ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∃ W : (A × unitInterval) ≃ₜ (c '' (A ×ˢ Icc (-ε) ε)),
      ∀ z, (W z : X) = c (z.1, (2 * (z.2 : ℝ) - 1) * ε) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have ht (z : A × unitInterval) : (2 * (z.2 : ℝ) - 1) * ε ∈ Icc (-ε) ε := by
    constructor <;> nlinarith [z.2.property.1, z.2.property.2]
  have hfull (z : A × unitInterval) :
      ((z.1 : E), (2 * (z.2 : ℝ) - 1) * ε) ∈ A ×ˢ Icc (-1 : ℝ) 1 := by
    exact ⟨z.1.property, ⟨by linarith [(ht z).1], by linarith [(ht z).2]⟩⟩
  let f : A × unitInterval → c '' (A ×ˢ Icc (-ε) ε) := fun z =>
    ⟨c (z.1, (2 * (z.2 : ℝ) - 1) * ε),
      ⟨((z.1 : E), (2 * (z.2 : ℝ) - 1) * ε), ⟨z.1.property, ht z⟩, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      have heq := hi (hfull z) (hfull w) (congrArg Subtype.val h)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq)
      · apply Subtype.ext
        have hh := congrArg Prod.snd heq
        dsimp at hh
        nlinarith
    · rintro ⟨x, ⟨a, t⟩, ⟨ha, ht⟩, rfl⟩
      have hpos : 0 < 2 * ε := by positivity
      let u : unitInterval := ⟨(t + ε) / (2 * ε),
        div_nonneg (by linarith [ht.1]) hpos.le,
        (div_le_iff₀ hpos).mpr (by linarith [ht.2])⟩
      refine ⟨(⟨a, ha⟩, u), Subtype.ext ?_⟩
      change c (a, (2 * ((t + ε) / (2 * ε)) - 1) * ε) = c (a, t)
      congr 1
      ext
      · rfl
      · field_simp; ring
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    exact hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub
          continuous_const).mul continuous_const)) hfull
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf) hfc, fun _ => rfl⟩

end PoincareConjecture.M76

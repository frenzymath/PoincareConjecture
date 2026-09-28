import PoincareConjecture.Proofs.M32.Mathlib.ProductCompactBoundary

set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.M32

theorem not_isCompact_of_product_graph_frontier
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    {U K : Set M} (hU : IsOpen U) (hKU : K ⊆ U) (e : U ≃ₜ X × ℝ)
    (h : X → ℝ) (hh : Continuous h) (hint : (interior K).Nonempty)
    (hfront : e '' ((Subtype.val : U → M) ⁻¹' frontier K) ⊆
      {z | z.2 = h z.1}) : ¬ IsCompact K := by
  let shear : (X × ℝ) ≃ₜ X × ℝ :=
    { toFun := fun z => (z.1, z.2 - h z.1)
      invFun := fun z => (z.1, z.2 + h z.1)
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hh.comp continuous_fst))
      continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hh.comp continuous_fst)) }
  apply not_isCompact_of_product_chart_frontier hU hKU (e.trans shear) (a := 0) hint
  rintro z ⟨y, hy, rfl⟩
  change (e y).2 - h (e y).1 = 0
  exact sub_eq_zero.mpr (hfront ⟨y, hy, rfl⟩)

end PoincareConjecture.M32

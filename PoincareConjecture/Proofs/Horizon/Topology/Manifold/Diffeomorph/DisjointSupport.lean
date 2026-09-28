import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners Real E H}

theorem mapsTo_of_eqOn_compl (D : Diffeomorph I I M M ∞) {U : Set M}
    (hfix : ∀ x, x ∉ U → D x = x) : MapsTo D U U := by
  intro x hx
  by_contra hDx
  have heq : D x = x := D.injective (hfix (D x) hDx)
  exact hDx (heq.symm ▸ hx)

theorem trans_eqOn_of_disjoint (D F : Diffeomorph I I M M ∞)
    {U V : Set M} (hUV : Disjoint U V)
    (hD : ∀ x, x ∉ U → D x = x) (hF : ∀ x, x ∉ V → F x = x) :
    EqOn (D.trans F) D U ∧ EqOn (D.trans F) F V := by
  constructor
  · intro x hx
    change F (D x) = D x
    apply hF
    exact fun hin => disjoint_left.mp hUV (D.mapsTo_of_eqOn_compl hD hx) hin
  · intro x hx
    change F (D x) = F x
    rw [hD x (fun hin => disjoint_left.mp hUV hin hx)]

theorem trans_preserves {A : Type*} (D F : Diffeomorph I I M M ∞)
    (h : M → A) (hD : ∀ x, h (D x) = h x) (hF : ∀ x, h (F x) = h x)
    (x : M) : h ((D.trans F) x) = h x :=
  (hF (D x)).trans (hD x)

theorem trans_compact_support_fin_two
    (D : Fin 2 → Diffeomorph I I M M ∞) (K U : Fin 2 → Set M)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hfix : ∀ i x, x ∉ K i → D i x = x) :
    IsCompact (K 0 ∪ K 1) ∧ K 0 ∪ K 1 ⊆ U 0 ∪ U 1 ∧
      (∀ x, x ∉ K 0 ∪ K 1 → ((D 0).trans (D 1)) x = x) ∧
      ∀ i, EqOn ((D 0).trans (D 1)) (D i) (U i) := by
  have hfixU (i : Fin 2) (x : M) (hx : x ∉ U i) : D i x = x :=
    hfix i x (fun hin => hx (hKU i hin))
  have hagree := (D 0).trans_eqOn_of_disjoint (D 1)
    (hU (by decide : (0 : Fin 2) ≠ 1)) (hfixU 0) (hfixU 1)
  refine ⟨(hK 0).union (hK 1), union_subset_union (hKU 0) (hKU 1), ?_, ?_⟩
  · intro x hx
    change D 1 (D 0 x) = x
    rw [hfix 0 x (fun hin => hx (Or.inl hin)),
      hfix 1 x (fun hin => hx (Or.inr hin))]
  · intro i
    fin_cases i
    · exact hagree.1
    · exact hagree.2

end Diffeomorph

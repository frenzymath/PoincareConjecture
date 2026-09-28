import PoincareConjecture.Proofs.M76.Brown.CellularShrinkingConstruction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.QuotientFibersHomeomorph










set_option autoImplicit false

open Set

namespace Homeomorph

variable {X Y E : Type*} [MetricSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]




theorem exists_of_cellular_fiber
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hnest : ∀ n, K (n + 1) ⊆ interior (K n))
    (hpair : ∀ n, IsUnitBallPair E (K n) (frontier (K n)))
    (f : C(X, Y)) (hf : Function.Surjective f)
    (hfib : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) :
    ∃ H : X ≃ₜ Y, EqOn H f (interior (K 0))ᶜ := by
  obtain ⟨g, hg, hgfib, hfix⟩ := exists_collapse_of_nested_ballPairs K hK hnest hpair
  have hqg := g.continuous.isClosedMap.isQuotientMap g.continuous hg
  have hqf := f.continuous.isClosedMap.isQuotientMap f.continuous hf
  obtain ⟨H, hHg⟩ := hqg.exists_homeomorph_of_fibers hqf
    (fun x y => (hgfib x y).trans (hfib x y).symm)
  refine ⟨H, ?_⟩
  intro x hx
  have heq := hHg x
  rwa [hfix hx] at heq

end Homeomorph

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]




theorem mem_set_iff_of_surjective_agreement (H : X ≃ₜ Y) {f : X → Y}
    (hf : Function.Surjective f) {P : Set X} {B : Set Y}
    (hH : EqOn H f P) (hmark : ∀ x, f x ∈ B ↔ x ∈ P) (x : X) :
    H x ∈ B ↔ x ∈ P := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hf (H x)
    have hyP : y ∈ P := (hmark y).mp (hy.symm ▸ hx)
    have hyx : y = x := H.injective ((hH hyP).trans hy)
    exact hyx ▸ hyP
  · intro hx
    rw [hH hx]
    exact (hmark x).mpr hx

end Homeomorph

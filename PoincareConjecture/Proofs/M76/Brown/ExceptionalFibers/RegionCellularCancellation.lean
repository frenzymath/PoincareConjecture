import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.CellularCancellation
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.SupportedFiberRegions

set_option autoImplicit false

open Set

namespace Homeomorph

variable {X Y E : Type*} [MetricSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_region_marked_of_disjoint_cellular_fibers
    (K L : ℕ → Set X) (hK : ∀ n, IsCompact (K n)) (hL : ∀ n, IsCompact (L n))
    (hnestK : ∀ n, K (n + 1) ⊆ interior (K n))
    (hnestL : ∀ n, L (n + 1) ⊆ interior (L n))
    (hpairK : ∀ n, IsUnitBallPair E (K n) (frontier (K n)))
    (hpairL : ∀ n, IsUnitBallPair E (L n) (frontier (L n)))
    (hdis : Disjoint (K 0) (L 0)) (f : C(X, Y)) (hf : Function.Surjective f)
    (hfib : ∀ x y, f x = f y ↔ x = y ∨
      ((x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∨ ((x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n)))
    {D P : Set X} {C B : Set Y} (hKD : K 0 ⊆ D) (hLD : L 0 ⊆ Dᶜ)
    (hP : P ⊆ (interior (K 0) ∪ interior (L 0))ᶜ)
    (hmark : ∀ x, f x ∈ B ↔ x ∈ P) (hregion : ∀ x, f x ∈ C ↔ x ∈ D) :
    ∃ H : X ≃ₜ Y, EqOn H f P ∧ (∀ x, H x ∈ B ↔ x ∈ P) ∧
      ∀ x, H x ∈ C ↔ x ∈ D := by
  classical
  obtain ⟨gA, hgA, hAfib, hfixA⟩ :=
    exists_collapse_of_nested_ballPairs K hK hnestK hpairK
  obtain ⟨gB, hgB, hBfib, hfixB⟩ :=
    exists_collapse_of_nested_ballPairs L hL hnestL hpairL
  have hgAD : ∀ x, gA x ∈ D ↔ x ∈ D :=
    Function.mem_set_iff_of_exceptional_fiber_fixed_compl gA
      ((iInter_subset K 0).trans hKD) hAfib (by
        intro x hx
        exact hfixA (fun hxK => hx (hKD (interior_subset hxK))))
  have hgBDc : ∀ x, gB x ∈ Dᶜ ↔ x ∈ Dᶜ :=
    Function.mem_set_iff_of_exceptional_fiber_fixed_compl gB
      ((iInter_subset L 0).trans hLD) hBfib (by
        intro x hx
        exact hfixB (fun hxL => hx (hLD (interior_subset hxL))))
  have hgBD (x : X) : gB x ∈ D ↔ x ∈ D := not_iff_not.mp (hgBDc x)
  have hBA : (⋂ n, L n) ⊆ (interior (K 0))ᶜ := by
    intro x hx hxK
    exact Set.disjoint_left.mp hdis (interior_subset hxK) (mem_iInter.mp hx 0)
  have hAB : Disjoint (⋂ n, K n) (⋂ n, L n) :=
    hdis.mono (iInter_subset K 0) (iInter_subset L 0)
  have hpreB (x : X) : gA x ∈ ⋂ n, L n ↔ x ∈ ⋂ n, L n := by
    constructor
    · intro hx
      have heq : gA x = gA (gA x) := (hfixA (hBA hx)).symm
      rcases (hAfib x (gA x)).mp heq with hxx | ⟨_, hyA⟩
      · exact hxx.symm ▸ hx
      · exact False.elim (Set.disjoint_left.mp hAB hyA hx)
    · intro hx
      rwa [hfixA (hBA hx)]
  let g : C(X, X) := gB.comp gA
  have hg : Function.Surjective g := hgB.comp hgA
  have hgD (x : X) : g x ∈ D ↔ x ∈ D := (hgBD (gA x)).trans (hgAD x)
  have hgfib (x y : X) : g x = g y ↔ x = y ∨
      ((x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∨ ((x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n)) := by
    change gB (gA x) = gB (gA y) ↔ _
    rw [hBfib, hAfib, hpreB, hpreB]
    exact or_assoc
  have hqg := g.continuous.isClosedMap.isQuotientMap g.continuous hg
  have hqf := f.continuous.isClosedMap.isQuotientMap f.continuous hf
  obtain ⟨H, hHg⟩ := hqg.exists_homeomorph_of_fibers hqf
    (fun x y => (hgfib x y).trans (hfib x y).symm)
  have hH : EqOn H f P := by
    intro x hx
    have hnotK : x ∉ interior (K 0) := fun h => hP hx (Or.inl h)
    have hnotL : x ∉ interior (L 0) := fun h => hP hx (Or.inr h)
    have hgfix : g x = x := by
      change gB (gA x) = x
      calc
        gB (gA x) = gB x := congrArg gB (hfixA hnotK)
        _ = x := hfixB hnotL
    have heq := hHg x
    rwa [hgfix] at heq
  refine ⟨H, hH, H.mem_set_iff_of_surjective_agreement hf hH hmark, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hg y
  rw [hHg x, hregion x, hgD x]

end Homeomorph

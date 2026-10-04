import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.General.ExceptionalFibers.CellularCancellation

/-!
# Cancel both actual disjoint cellular fibers in the compact ambient space

The two collapse maps are constructed on the same compact metric space.
Disjoint first cells make their composite's fiber relation exact and
preserve every point outside both cell interiors. Quotient cancellation
therefore retains the complete marked middle sphere.
See Brown1960 Theorems2, 4--5 and Brown derivation016, section4.
-/

set_option autoImplicit false

open Set

namespace Homeomorph

variable {X Y E : Type*} [MetricSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Construct the ambient homeomorphism cancelling two actual disjoint
cellular fibers. Their nested ball models and the original quotient
are displayed; none is inferred from a separation statement.
See Brown derivation016, section4. -/
theorem exists_of_disjoint_cellular_fibers
    (K L : ℕ → Set X) (hK : ∀ n, IsCompact (K n)) (hL : ∀ n, IsCompact (L n))
    (hnestK : ∀ n, K (n + 1) ⊆ interior (K n))
    (hnestL : ∀ n, L (n + 1) ⊆ interior (L n))
    (hpairK : ∀ n, IsUnitBallPair E (K n) (frontier (K n)))
    (hpairL : ∀ n, IsUnitBallPair E (L n) (frontier (L n)))
    (hdis : Disjoint (K 0) (L 0)) (f : C(X, Y)) (hf : Function.Surjective f)
    (hfib : ∀ x y, f x = f y ↔ x = y ∨
      ((x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∨ ((x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n))) :
    ∃ H : X ≃ₜ Y, EqOn H f (interior (K 0) ∪ interior (L 0))ᶜ := by
  obtain ⟨gA, hgA, hAfib, hfixA⟩ :=
    exists_collapse_of_nested_ballPairs K hK hnestK hpairK
  obtain ⟨gB, hgB, hBfib, hfixB⟩ :=
    exists_collapse_of_nested_ballPairs L hL hnestL hpairL
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
  have hgfib (x y : X) : g x = g y ↔ x = y ∨
      ((x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∨ ((x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n)) := by
    change gB (gA x) = gB (gA y) ↔ _
    rw [hBfib, hAfib, hpreB, hpreB]
    exact or_assoc
  have hqg := g.continuous.isClosedMap.isQuotientMap g.continuous hg
  have hqf := f.continuous.isClosedMap.isQuotientMap f.continuous hf
  obtain ⟨H, hHg⟩ := hqg.exists_homeomorph_of_fibers hqf
    (fun x y => (hgfib x y).trans (hfib x y).symm)
  refine ⟨H, ?_⟩
  intro x hx
  have hnotK : x ∉ interior (K 0) := fun h => hx (Or.inl h)
  have hnotL : x ∉ interior (L 0) := fun h => hx (Or.inr h)
  have hgfix : g x = x := by
    change gB (gA x) = x
    calc
      gB (gA x) = gB x := congrArg gB (hfixA hnotK)
      _ = x := hfixB hnotL
  have heq := hHg x
  rwa [hgfix] at heq

/-- The actual two-fiber cancellation preserves the complete marked
middle set in both directions. See Brown derivation016, sections3--4. -/
theorem exists_marked_of_disjoint_cellular_fibers
    (K L : ℕ → Set X) (hK : ∀ n, IsCompact (K n)) (hL : ∀ n, IsCompact (L n))
    (hnestK : ∀ n, K (n + 1) ⊆ interior (K n))
    (hnestL : ∀ n, L (n + 1) ⊆ interior (L n))
    (hpairK : ∀ n, IsUnitBallPair E (K n) (frontier (K n)))
    (hpairL : ∀ n, IsUnitBallPair E (L n) (frontier (L n)))
    (hdis : Disjoint (K 0) (L 0)) (f : C(X, Y)) (hf : Function.Surjective f)
    (hfib : ∀ x y, f x = f y ↔ x = y ∨
      ((x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∨ ((x ∈ ⋂ n, L n) ∧ (y ∈ ⋂ n, L n)))
    {P : Set X} {B : Set Y} (hP : P ⊆ (interior (K 0) ∪ interior (L 0))ᶜ)
    (hmark : ∀ x, f x ∈ B ↔ x ∈ P) :
    ∃ H : X ≃ₜ Y, EqOn H f P ∧ ∀ x, H x ∈ B ↔ x ∈ P := by
  obtain ⟨H, hH⟩ := exists_of_disjoint_cellular_fibers K L hK hL hnestK hnestL
    hpairK hpairL hdis f hf hfib
  exact ⟨H, hH.mono hP, H.mem_set_iff_of_surjective_agreement hf (hH.mono hP) hmark⟩

end Homeomorph

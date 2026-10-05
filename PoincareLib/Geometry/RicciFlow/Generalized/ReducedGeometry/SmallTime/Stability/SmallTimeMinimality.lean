import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SmallTime.Coordinates.SmallTimeGaugeComparison
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential

/-!
# From low-action comparison to genuine unique minimizing branches

Morgan-Tian Corollary 6.79, pp. 144-145. It suffices to compare
competitors whose action is at most the selected path's action.
This gives global minimality and uniqueness without any prior
attainment assumption. Coherence then supplies the exact frozen
unique-minimizing-branch predicate for the exponential family.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

/-- Comparison against every low-action competitor proves genuine
global minimality and uniqueness, the confinement implication in
Corollary 6.79, pp. 144-145. -/
theorem minimizing_and_unique_of_lowAction_comparison
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hcompare : ∀ q : M14BackwardPath G T τ₁ τ₂ x y,
      M14BackwardLAction G q ≤ M14BackwardLAction G p →
        M14BackwardLAction G p ≤ M14BackwardLAction G q ∧ EqOn q.curve p.curve (Icc τ₁ τ₂)) :
    M14IsMinimizing p ∧ ∀ q : M14BackwardPath G T τ₁ τ₂ x y,
      M14IsMinimizing q → EqOn q.curve p.curve (Icc τ₁ τ₂) := by
  refine ⟨fun q => ?_, fun q hq => (hcompare q (hq p)).2⟩
  exact (le_total (M14BackwardLAction G p) (M14BackwardLAction G q)).elim id
    (fun hq => (hcompare q hq).1)

/-- Genuine minimality and uniqueness of a supplied selected path
give the exact frozen branch predicate, Corollary 6.79, pp. 144-145. -/
theorem uniqueMinimizingBranch_of_selected_path
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hmin : M14IsMinimizing (E.path Z s hs hpos))
    (hunique : ∀ q : M14BackwardPath G T 0 (s ^ 2) x (E.gamma Z s),
      M14IsMinimizing q → EqOn q.curve (E.path Z s hs hpos).curve (Icc 0 (s ^ 2))) :
    M14UniqueMinimizingBranch G T (s ^ 2) x E Z := by
  unfold M14UniqueMinimizingBranch
  rw [Real.sqrt_sq hpos.le]
  exact ⟨hs, E.path Z s hs hpos, E.path_coherent Z s hs hpos, hmin, hunique⟩

end PoincareMT.M14

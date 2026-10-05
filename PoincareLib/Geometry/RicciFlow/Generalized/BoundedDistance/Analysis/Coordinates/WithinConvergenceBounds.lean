import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.WithinJetBounds

/-!
# Finite uniform bounds from converging within jets

Compact convergence of actual within derivatives to a smooth function
gives one eventual bound for any finite list of orders. This is used
for coordinate correction in Morgan--Tian Proposition 5.14, pp. 90-91;
see task derivation 09.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

/-- Compact-uniform convergence to a continuous limit gives an eventual
uniform norm bound, with a positive common constant (derivation 09). -/
theorem TendstoUniformlyOn.exists_eventual_norm_bound
    {E F α : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    {l : Filter α} {f : α → E → F} {g : E → F} {K : Set E}
    (h : TendstoUniformlyOn f g l K) (hK : IsCompact K) (hg : ContinuousOn g K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ k in l, ∀ x ∈ K, ‖f k x‖ ≤ C := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg
  refine ⟨max (B + 1) 1, le_max_right _ _, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h 1 zero_lt_one] with k hk x hx
  apply le_trans ?_ (le_max_left _ _)
  calc
    ‖f k x‖ = ‖g x + (f k x - g x)‖ := by rw [add_sub_cancel]
    _ ≤ ‖g x‖ + ‖f k x - g x‖ := norm_add_le _ _
    _ ≤ B + 1 := add_le_add (hB x hx) (by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le)

/-- All within jets through a fixed order admit one eventual compact
bound when those actual jets converge to a smooth limit (derivation 09). -/
theorem exists_eventual_withinJet_bound_of_tendstoUniformlyOn
    {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter α} {S K : Set E} {f : α → E → F} {g : E → F}
    (hS : UniqueDiffOn ℝ S) (hg : ContDiffOn ℝ ∞ g S)
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjets : ∀ r, TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ r (f k) S)
      (iteratedFDerivWithin ℝ r g S) l K) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ k in l, ∀ r ≤ m, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ r (f k) S x‖ ≤ C := by
  have hsingle (r : ℕ) := (hjets r).exists_eventual_norm_bound hK
    ((hg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)) hS).mono hKS)
  induction m with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := hsingle 0
      exact ⟨C, hC, hbound.mono fun k hk r hr x hx => by
        have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
        subst r
        exact hk x hx⟩
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      obtain ⟨B, hB, hlast⟩ := hsingle (m + 1)
      refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
      filter_upwards [hbound, hlast] with k hk hl r hr x hx
      rcases Nat.le_or_eq_of_le_add_one hr with hr | rfl
      · exact (hk r hr x hx).trans (le_max_left _ _)
      · exact (hl x hx).trans (le_max_right _ _)

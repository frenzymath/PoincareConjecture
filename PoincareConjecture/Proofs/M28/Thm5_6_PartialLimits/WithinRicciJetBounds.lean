import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution
import PoincareConjecture.Proofs.M28.Mathlib.WithinBoundsFromInterior

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds

open Bootstrap

theorem eventuallyBounded_within_ricci_spacetime_jets
    {n : ℕ} {α : Type*} (l : Filter α)
    (f : α → ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n)
    (J : α → Set ℝ) (U : α → Set (EuclideanSpace ℝ (Fin n)))
    (T S : α → Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hJ : ∀ w, UniqueDiffOn ℝ (J w)) (hU : ∀ w, IsOpen (U w))
    (hf : ∀ w, ContDiffOn ℝ ∞ (f w) (J w ×ˢ U w))
    (hT : ∀ w, T w ⊆ interior (J w) ×ˢ U w)
    (hS : ∀ w, S w ⊆ (J w ×ˢ U w) ∩ closure (T w))
    (hrange : ∀ w z, z ∈ interior (J w) ×ˢ U w →
      spatialJet 2 (f w) z ∈ jetRicciFlowDomain n)
    (hevol : ∀ w z, z ∈ interior (J w) ×ˢ U w →
      deriv (fun t => f w (t, z.2)) z.1 =
        jetRicciFlowOperator n (spatialJet 2 (f w) z))
    (hspatial : ∀ q, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ T w, ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j (fun x => f w (z.1, x)) z.2‖ ≤ B)
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ᶠ w in l, ∀ z ∈ T w, ∀ v, a * ‖v‖ ^ 2 ≤ f w z v v) :
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ S w,
      ‖iteratedFDerivWithin ℝ m (f w) (J w ×ˢ U w) z‖ ≤ B := by
  have hcompact (j : ℕ) :
      ∃ K : Set (Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + j)),
        IsCompact K ∧ K ⊆ (baseProjection 2 j) ⁻¹' jetRicciFlowDomain n ∧
        ∀ᶠ w in l, MapsTo (spatialJet (2 + j) (f w)) (T w) K := by
    obtain ⟨B, hB, hbound⟩ := hspatial (2 + j)
    obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n j ha B
    refine ⟨K, hK, hKU, ?_⟩
    filter_upwards [hbound, hell] with w hw he z hz
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hw z hz d (by omega))
    · exact he z hz
  have hsingle (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ T w,
      ‖iteratedFDeriv ℝ j (fun x => f w (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hspatial j
    exact ⟨B, hB, hb.mono (fun w hw z hz => hw z hz j le_rfl)⟩
  intro m
  obtain ⟨B, hB, hb⟩ := eventuallyBounded_spacetime_jets l
    (isOpen_jetRicciFlowDomain n) (contDiffOn_jetRicciFlowOperator n)
    f (fun w => interior (J w)) U T
    (fun w => (hf w).mono (prod_mono interior_subset Subset.rfl))
    (fun _ => isOpen_interior) hU hT hrange hevol hsingle hcompact m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb] with w hw z hz
  apply norm_iteratedFDerivWithin_le_of_interior_bound (hf w)
    ((hJ w).prod (hU w).uniqueDiffOn)
    (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
    (T := T w) ?_ hw (hS w hz).1 (hS w hz).2
  simpa only [interior_prod_eq, (hU w).interior_eq] using hT w

end PoincareConjecture.SpacetimeBounds

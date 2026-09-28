import PoincareConjecture.Proofs.M34.Thm12_5_Existence.ApproximationEvolution











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.CompactCapApproximation

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {g0 : StandardInitialMetric} (A : CompactCapApproximation g0)

set_option synthInstance.maxHeartbeats 100000 in



theorem eventually_compact_spacetimeJet_bound (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ t ∈ Ioo 0 A.time,
      ∀ x ∈ K, x ∈ compactCapSource g0 k →
        ‖iteratedFDeriv ℝ m
          (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2) (t, x)‖ ≤ B := by
  let f := fun k (p : ℝ × StandardCapSpace) => A.coefficients k p.1 p.2
  let S := fun k => Ioo 0 A.time ×ˢ (K ∩ compactCapSource g0 k)
  have hspatial (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ S k, ‖iteratedFDeriv ℝ j (fun x => f k (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ := A.exists_compact_spatialJet_bounds P hK j
    exact ⟨B, zero_le_one.trans hB, Eventually.of_forall
      (fun k z hz => hbound j le_rfl k z.1 (Ioo_subset_Icc_self hz.1) z.2 hz.2.1 hz.2.2)⟩
  have hcompact (j : ℕ) :
      ∃ L : Set (Jet StandardCapSpace (MetricCoefficient 3) (2 + j)),
        IsCompact L ∧ L ⊆ (baseProjection 2 j) ⁻¹' jetRicciFlowDomain 3 ∧
          ∀ᶠ k : ℕ in atTop, MapsTo (spatialJet (2 + j) (f k)) (S k) L := by
    obtain ⟨L, hL, hLU, hrange⟩ := A.exists_compact_spatialJet_box P hK j
    exact ⟨L, hL, hLU, Eventually.of_forall
      (fun k z hz => hrange k z.1 (Ioo_subset_Icc_self hz.1) z.2 hz.2.1 hz.2.2)⟩
  obtain ⟨B, hB, hbound⟩ := eventuallyBounded_spacetime_jets atTop
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    f (fun _ => Ioo 0 A.time) (compactCapSource g0) S
    (A.contDiffOn_interior_coefficients) (fun _ => isOpen_Ioo)
    (compactCapSource_isOpen g0) (fun _ _ hz => ⟨hz.1, hz.2.2⟩)
    (fun k z hz => A.spatialJet_mem_domain k z.1 hz.2)
    (fun k z hz => A.deriv_coefficients_eq_operator k hz.1 hz.2) hspatial hcompact m
  refine ⟨B, hB, hbound.mono ?_⟩
  intro k hk t ht x hx hsource
  exact hk (t, x) ⟨ht, hx, hsource⟩

end PoincareConjecture.M34.CompactCapApproximation

import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds SpacetimeBounds.Bootstrap

theorem eventually_coordinate_spacetime_jet_bound
    {alpha : Type*} (l : Filter alpha) (n : ℕ)
    (f : alpha → ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n)
    (J : alpha → Set ℝ) (U : alpha → Set (EuclideanSpace ℝ (Fin n)))
    (S : alpha → Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hsmooth : ∀ k, ContDiffOn ℝ ∞ (f k) (J k ×ˢ U k))
    (hJ : ∀ k, IsOpen (J k)) (hU : ∀ k, IsOpen (U k))
    (hS : ∀ k, S k ⊆ J k ×ˢ U k)
    (hinvertible : ∀ k p, p ∈ J k ×ˢ U k → (f k p).IsInvertible)
    (hevolution : ∀ k t, t ∈ J k → ∀ x ∈ U k,
      HasDerivAt (fun s => f k (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => f k (t, y)) x)) t)
    {a : ℝ} (ha : 0 < a)
    (helliptic : ∀ᶠ k in l, ∀ p ∈ S k, ∀ v,
      a * ‖v‖ ^ 2 ≤ f k p v v)
    (hspatial : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ p ∈ S k, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun x => f k (p.1, x)) p.2‖ ≤ B) :
    ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ p ∈ S k, ‖iteratedFDeriv ℝ m (f k) p‖ ≤ B := by
  apply eventuallyBounded_spacetime_jets l
    (isOpen_jetRicciFlowDomain n) (contDiffOn_jetRicciFlowOperator n)
    f J U S hsmooth hJ hU hS
  · intro k p hp
    change ((twoJetProjection n (spatialJet 2 (f k) p)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact hinvertible k p hp
  · intro k p hp
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact (hevolution k p.1 hp.1 p.2 hp.2).deriv
  · intro j
    obtain ⟨B, hB, hbound⟩ := hspatial j
    exact ⟨B, hB, hbound.mono fun k hk p hp => hk p hp j le_rfl⟩
  · intro j
    obtain ⟨B, hB, hbound⟩ := hspatial (2 + j)
    obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n j ha B
    refine ⟨K, hK, hKU, ?_⟩
    filter_upwards [hbound, helliptic] with k hk hell p hp
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hk p hp d (by omega))
    · exact hell p hp

end PoincareConjecture.M44

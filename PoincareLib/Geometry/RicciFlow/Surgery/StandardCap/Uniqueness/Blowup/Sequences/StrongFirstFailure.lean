import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Sequences.FirstFailure
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Sequences.BlowupSequence

/-!
# First failure of full strong canonical control

Morgan-Tian Theorem 12.28, pp. 323-324, and Theorem 11.1, pp. 267-269.
Select the original points using full Chapter 9 certificates. All earlier
points above four times the base scalar then have exactly the strong
canonical control used by M30, including its full cap data.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28: unbounded failure of strong canonical control
produces an actual diverging sequence satisfying M30's earlier canonical
hypothesis, with failure retained at each original selected basepoint. -/
theorem exists_strong_first_failure_sequence (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (epsilon C H₀ : ℝ) (hH₀ : 0 < H₀)
    (hbad : ∀ B : ℝ, 0 < B → ∃ t, ∃ ht : t ∈ Ico 0 E.flow.base.lifetime,
      ∃ x : StandardCapSpace, B ≤ (E.flow.connection t).scalarCurvature x ∧
        ¬GeneralizedCanonicalControl (F := generalizedFlow E.flow.base.flow)
          t ((sliceDiffeomorph ht).symm x) epsilon C) :
    ∃ (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop),
      (∀ k : ℕ, H₀ + (k : ℝ) ≤ (E.flow.connection (t k)).scalarCurvature (x k)) ∧
      (∀ k, ¬GeneralizedCanonicalControl (F := generalizedFlow E.flow.base.flow)
        (t k) ((sliceDiffeomorph (ht k)).symm (x k)) epsilon C) ∧
      ∀ k, generalizedEarlierStrongCanonicalNeighborhoods
        ((blowupSequence P E t x ht hR).flow k) epsilon C
        ((blowupSequence P E t x ht hR).base k).1
        ((blowupSequence P E t x ht hR).base k).2 := by
  let Good (t : ℝ) (x : StandardCapSpace) : Prop :=
    ∀ ht : t ∈ Ico 0 E.flow.base.lifetime,
      GeneralizedCanonicalControl (F := generalizedFlow E.flow.base.flow)
        t ((sliceDiffeomorph ht).symm x) epsilon C
  have hbad' : ∀ B : ℝ, 0 < B → ∃ t ∈ Ico 0 E.flow.base.lifetime,
      ∃ x : StandardCapSpace, B ≤ (E.flow.connection t).scalarCurvature x ∧ ¬Good t x := by
    intro B hB
    obtain ⟨t, ht, x, hx, hbadx⟩ := hbad B hB
    exact ⟨t, ht, x, hx, fun h => hbadx (h ht)⟩
  obtain ⟨t, x, ht, hx, hbadx, hR, hprior⟩ :=
    exists_first_failure_sequence E.flow Good H₀ hH₀ hbad'
  refine ⟨t, x, ht, hR, hx, ?_, ?_⟩
  · intro k hgood
    exact hbadx k (fun _ => hgood)
  · intro k s hs hst y hhigh
    have hscale := scalar_eq P E.flow.base.flow (ht k) (x k)
    have hscalar := scalar_eq P E.flow.base.flow hs y.val
    have hhigh' : 4 * (E.flow.connection (t k)).scalarCurvature (x k) ≤
        (E.flow.connection s).scalarCurvature y.val := by
      exact (congrArg (fun r : ℝ => 4 * r) hscale).symm ▸ (hscalar ▸ hhigh)
    exact ⟨hprior k s hs hst y.val hhigh' hs⟩

end PoincareMT.M35.OrdinaryRealization

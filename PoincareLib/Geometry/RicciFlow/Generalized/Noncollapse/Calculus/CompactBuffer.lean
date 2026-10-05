import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Mathlib/CompactBuffer.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Compact balls inside an embedded spatial buffer

The initial-time buffer needed in Morgan-Tian Claim 8.5, p. 172, as
recorded in `references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-compact-buffer.md`.
Only a radial distance bound and compact closure of the target ball are
used. No completeness or Hausdorff assumption is needed.
-/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal Topology

namespace Metric

/-- A radial distance bound inside a compact target buffer makes the source
ball precompact. This is the topological step in corrected Claim 8.5,
Morgan-Tian p. 172. -/
theorem isCompact_closure_eball_of_isEmbedding
    {C N : Type*} [PseudoEMetricSpace C] [PseudoEMetricSpace N]
    {f : C → N} (hf : Topology.IsEmbedding f) {x : N} {c : C}
    {R r₀ r₁ ρ : ℝ≥0∞} {L : ℝ≥0}
    (hrange : range f = eball x R)
    (hcompact : IsCompact (closure (eball x R)))
    (hc : edist x (f c) ≤ r₀)
    (hbound : ∀ z, edist (f c) (f z) ≤ (L : ℝ≥0∞) * edist c z)
    (hbuffer : r₀ + (L : ℝ≥0∞) * ρ ≤ r₁) (hsmall : r₁ < R) :
    IsCompact (closure (eball c ρ)) := by
  have hsub : closedEBall x r₁ ⊆ eball x R :=
    fun _ hz => (mem_closedEBall.mp hz).trans_lt hsmall
  have hK : IsCompact (closedEBall x r₁) :=
    hcompact.of_isClosed_subset isClosed_closedEBall (hsub.trans subset_closure)
  have hKr : closedEBall x r₁ ⊆ range f := by
    rw [hrange]
    exact hsub
  have hpre := hf.isInducing.isCompact_preimage' hK hKr
  apply hpre.of_isClosed_subset isClosed_closure
  intro z hz
  have hz' : z ∈ closedEBall c ρ :=
    (closure_minimal eball_subset_closedEBall isClosed_closedEBall) hz
  apply mem_closedEBall'.mpr
  calc
    edist x (f z) ≤ edist x (f c) + edist (f c) (f z) := edist_triangle _ _ _
    _ ≤ r₀ + (L : ℝ≥0∞) * ρ :=
      add_le_add hc ((hbound z).trans (mul_le_mul_right (mem_closedEBall'.mp hz') _))
    _ ≤ r₁ := hbuffer

end Metric

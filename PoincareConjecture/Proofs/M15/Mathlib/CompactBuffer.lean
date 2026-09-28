import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas










set_option autoImplicit false

open Set
open scoped ENNReal NNReal Topology

namespace Metric




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

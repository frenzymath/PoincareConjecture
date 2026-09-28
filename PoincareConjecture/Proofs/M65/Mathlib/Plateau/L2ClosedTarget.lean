import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false

open Filter Set
open scoped Topology ENNReal

namespace MeasureTheory.Lp

theorem ae_mem_of_tendsto_of_isClosed
    {X E : Type*} [MeasurableSpace X] {mu : Measure X}
    [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {K : Set E} (hK : IsClosed K) {u : ℕ → Lp E p mu} {u0 : Lp E p mu}
    (hconv : Tendsto u atTop (𝓝 u0))
    (hmem : ∀ n, ∀ᵐ x ∂mu, u n x ∈ K) : ∀ᵐ x ∂mu, u0 x ∈ K := by
  obtain ⟨phi, _, hphi⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hmem, hphi] with x hx hphix
  exact hK.mem_of_tendsto hphix (Eventually.of_forall fun n => mem_iInter.mp hx (phi n))

end MeasureTheory.Lp

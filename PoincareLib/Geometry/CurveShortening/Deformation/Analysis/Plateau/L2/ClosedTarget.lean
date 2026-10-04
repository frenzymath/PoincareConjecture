import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closed target constraints survive strong Lp convergence

The embedded-target constraint in Morrey's Plateau construction,
ICM pp. 183-185, used for Morgan--Tian Lemma 19.2, pp. 437-439.
An actual AE-convergent subsequence retains the pointwise closed target;
no continuity of the limit map is inferred. See M65 derivation 27.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology ENNReal

namespace MeasureTheory.Lp

/-- Strong Lp convergence preserves an almost-everywhere closed target
constraint. The AE subsequence is extracted from the supplied convergence;
Morrey ICM pp. 183-185 and MT Lemma 19.2, pp. 437-439. -/
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

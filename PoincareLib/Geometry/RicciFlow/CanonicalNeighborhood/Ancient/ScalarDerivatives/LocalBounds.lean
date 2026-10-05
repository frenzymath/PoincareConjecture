import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Services

/-!
# Uniform local scalar bounds on normalized ancient solutions

The sequence-wise local estimate supplied by normalized compactness is uniform
over all based solutions with the same positive noncollapsing constant. A
sequence violating uniformity would violate its own local estimate.

Reference: Morgan--Tian, Lemma 9.65 and Corollary 9.71, pp. 225-230.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.ScalarDerivatives

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

/-- The constant precedes every based normalized solution, including its carrier. -/
theorem uniform_based_local_scalar_bound
    (S : ScalarDerivativeServices.{u}) {kappa : ℝ} (hkappa : 0 < kappa)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : BasedKappaSolution kappa,
      ∀ x ∈ (B.flow.flow.metric 0).ball B.base r,
        (B.flow.flow.connection 0).scalarCurvature x ≤ C := by
  classical
  by_contra h
  push Not at h
  have hbad : ∀ n : ℕ, ∃ B : BasedKappaSolution kappa,
      ∃ x : B.carrier.carrier, x ∈ (B.flow.flow.metric 0).ball B.base r ∧
        (n : ℝ) + 1 < (B.flow.flow.connection 0).scalarCurvature x := by
    intro n
    exact h ((n : ℝ) + 1) (by positivity)
  choose B x hx hR using hbad
  let seq : NormalizedKappaSolutionSequence kappa := ⟨hkappa, B⟩
  obtain ⟨T⟩ := S.normalized_compactness ⟨kappa, hkappa, seq⟩
  obtain ⟨C, _, hC⟩ := T.local_curvature_estimate r hr
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hb := hC n (x n) (hx n)
  have hnR := hR n
  change ((B n).flow.flow.connection 0).scalarCurvature (x n) ≤ C at hb
  linarith

end PoincareMT.ScalarDerivatives

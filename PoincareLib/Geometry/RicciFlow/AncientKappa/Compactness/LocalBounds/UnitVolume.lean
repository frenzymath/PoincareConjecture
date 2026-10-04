import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.FiniteRadius

/-!
# Local curvature control from one positive unit-ball volume

The finite-radius estimate supplies uniform whole-past curvature bounds
on every terminal base ball in any fixed-kappa family with a common positive
unit-ball volume. Scalar normalization is not required; this applies to
the secondary volume-normalized sequence in the local compactness proof.

Reference: Morgan--Tian Lemma 9.65 and Claim 9.66, pp. 225-227.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance unitVolumeCarrierConnected (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

/-- A positive unit-ball volume gives local whole-past full-curvature
control, uniformly over all actual fixed-kappa solutions and basepoints. -/
theorem m23_exists_local_curvature_bound_of_unit_ball_volume
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ ν R : ℝ} (hκ : 0 < κ) (hν : 0 < ν) (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (C : FlowCarrier.{0} 3) (K : AncientKappaSolution 3 C.carrier),
      K.kappa = κ → ∀ p : C.carrier,
      ENNReal.ofReal ν ≤ calibratedMetricVolume (K.flow.metric 0)
        ((K.flow.metric 0).ball p 1) →
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ (K.flow.metric 0).ball p R,
        |(K.flow.connection t).curvatureTensorNorm x| ≤ B := by
  have hRp : 0 < R + 1 := by linarith
  obtain ⟨A, hA, hcurv⟩ := m23_exists_curvature_bound_of_volume_lower_bound
    P hκ (div_pos hν (pow_pos hRp 3))
  refine ⟨A / (R + 1) ^ 2, div_nonneg hA (sq_nonneg _), ?_⟩
  intro C K hkappa p hvolume t ht x hx
  have hunit : (K.flow.metric 0).ball p 1 ⊆ (K.flow.metric 0).ball p (R + 1) := by
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hvolume' : ENNReal.ofReal ((ν / (R + 1) ^ 3) * (R + 1) ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (R + 1)) := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hRp.ne')]
    exact hvolume.trans (MeasureTheory.measure_mono hunit)
  have hx' : x ∈ (K.flow.metric 0).ball p (R + 1) :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (by linarith))
  have hscalar : (K.flow.connection 0).scalarCurvature x ≤ A / (R + 1) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
    simpa only [mul_comm] using hcurv C K hkappa p x (R + 1) hRp hx' hvolume'
  rw [abs_of_nonneg (show 0 ≤ (K.flow.connection t).curvatureTensorNorm x from
    Real.sqrt_nonneg _)]
  exact (P.past_norm_le_scalar C.carrier K t 0 ht le_rfl x).trans hscalar

end PoincareMT

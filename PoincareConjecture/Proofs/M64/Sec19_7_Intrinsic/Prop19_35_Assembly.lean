import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m64Intrinsic_length_loss_budget
    {L L₂ c f a : ℝ}
    (hL : 0 ≤ L)
    (hc : c ≤ L / 50)
    (hf : f ≤ 3 * L / 50)
    (ha : a ≤ L / 10)
    (hremaining : L - c - f - a ≤ L₂) :
    (3 / 4 : ℝ) * L ≤ L₂ := by
  linarith

theorem m64Intrinsic_total_loss_budget
    {L L₂ e : ℝ}
    (hL : 0 ≤ L)
    (he : e ≤ (9 : ℝ) * L / 50)
    (hremaining : L - e ≤ L₂) :
    (3 / 4 : ℝ) * L ≤ L₂ := by
  linarith

structure M64IntrinsicLengthLossWitness (N : IntrinsicAnnulus)
    (delta r K mu : ℝ) where
  first_length : ℝ
  first_length_eq : first_length =
    intrinsicBoundaryLength N.metric 1 0 rampPeriod
  curvature_loss : ℝ
  focusing_loss : ℝ
  area_loss : ℝ
  curvature_loss_bound : curvature_loss ≤ first_length / 50
  focusing_loss_bound : focusing_loss ≤ 3 * first_length / 50
  area_loss_bound : area_loss ≤ first_length / 10
  remaining_length :
    first_length - curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod

theorem m64Intrinsic_length_loss_witness_of_explicit_losses
    (N : IntrinsicAnnulus) (delta r K mu : ℝ)
    (curvature_loss focusing_loss area_loss : ℝ)
    (hcurvature : curvature_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (hfocusing : focusing_loss ≤
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (harea : area_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10)
    (hremaining : intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod) :
    Nonempty (M64IntrinsicLengthLossWitness N delta r K mu) := by
  exact ⟨{
    first_length := intrinsicBoundaryLength N.metric 1 0 rampPeriod
    first_length_eq := rfl
    curvature_loss := curvature_loss
    focusing_loss := focusing_loss
    area_loss := area_loss
    curvature_loss_bound := hcurvature
    focusing_loss_bound := hfocusing
    area_loss_bound := harea
    remaining_length := hremaining
  }⟩

theorem m64Intrinsic_comparison_of_explicit_losses
    (N : IntrinsicAnnulus) {r : ℝ} (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (curvature_loss focusing_loss area_loss : ℝ)
    (hcurvature : curvature_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (hfocusing : focusing_loss ≤
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (harea : area_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10)
    (hremaining : intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod) :
    (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
  have hL : 0 ≤ intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
    linarith
  exact m64Intrinsic_length_loss_budget hL hcurvature hfocusing harea hremaining

def M64IntrinsicLengthLossEstimates : Prop :=
  ∀ delta r K : ℝ, 0 < delta → delta < 1 / 100 → 0 < r →
    ∃ mu : ℝ, 0 < mu ∧
      ∀ N : IntrinsicAnnulus,
        N.GaussianCurvatureBound K →
        r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
        N.SmallBoundaryTurning delta r →
        intrinsicAnnulusArea N.metric < mu →
          Nonempty (M64IntrinsicLengthLossWitness N delta r K mu)

theorem m64IntrinsicAnnulusComparison_of_length_loss_estimates
    (h : M64IntrinsicLengthLossEstimates) :
    M64IntrinsicAnnulusComparison := by
  intro delta r K hdelta_pos hdelta_small hr
  obtain ⟨mu, hmu_pos, hmu⟩ := h delta r K hdelta_pos hdelta_small hr
  refine ⟨mu, hmu_pos, ?_⟩
  intro N hcurv hfirst hturn harea
  obtain ⟨W⟩ := hmu N hcurv hfirst hturn harea
  have hL : 0 ≤ W.first_length := by
    rw [W.first_length_eq]
    linarith [hr, hfirst]
  have hbound := m64Intrinsic_length_loss_budget hL
    W.curvature_loss_bound W.focusing_loss_bound W.area_loss_bound
    W.remaining_length
  simpa [W.first_length_eq] using hbound

end PoincareConjecture

import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.LipschitzGreen
import Mathlib.MeasureTheory.Group.Prod

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem smooth_of_supported (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact (hf z (hs hz)).contDiffAt (hU.mem_nhds (hs hz))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem integral_density_flux_eq_neg
    (hU : IsOpen U) {u w : Spacetime n → ℝ} {Cu Cw : ℝ≥0}
    (hu : LipschitzOnWith Cu u U) (hw : LipschitzOnWith Cw w U)
    {A : Fin n → Fin n → Spacetime n → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U)
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    let Q := fun i z => ∑ j, A i j z * spatialDeriv j φ z
    Integrable (fun z => timeDeriv w z * φ z + ∑ i, spatialDeriv i u z * Q i z) ∧
    Integrable (fun z => w z * timeDeriv φ z + u z * ∑ i, spatialDeriv i (Q i) z) ∧
    (∫ z, timeDeriv w z * φ z + ∑ i, spatialDeriv i u z * Q i z) =
      -(∫ z, w z * timeDeriv φ z + u z * ∑ i, spatialDeriv i (Q i) z) := by
  classical
  let Q := fun i z => ∑ j, A i j z * spatialDeriv j φ z
  have hd (j) : ContDiff ℝ ∞ (spatialDeriv j φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hQs (i) : tsupport (Q i) ⊆ tsupport φ := by
    apply closure_minimal ?_ (isClosed_tsupport φ)
    intro z hz
    by_contra hzφ
    have hzj (j) : spatialDeriv j φ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hzφ (tsupport_fderiv_apply_subset ℝ (spatialDirection j) h))
    exact hz (by simp only [Q, hzj, mul_zero, Finset.sum_const_zero])
  have hQc (i) : HasCompactSupport (Q i) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) (hQs i)
  have hQ (i) : ContDiff ℝ ∞ (Q i) := by
    apply smooth_of_supported hU ?_ ((hQs i).trans hφU)
    exact ContDiffOn.sum (fun j _ => (hA i j).mul (hd j).contDiffOn)
  have ht := WeakDerivative.integral_mul_fderiv_eq_neg volume hU hw hφ hφc hφU (0, 1)
  have hs := WeakDerivative.integral_mul_sum_fderiv_eq_neg volume hU hu spatialDirection Q
    hQ hQc (fun i => (hQs i).trans hφU)
  refine ⟨ht.1.add hs.1, ht.2.1.add hs.2.1, ?_⟩
  change (∫ z, fderiv ℝ w z (0, 1) * φ z +
      ∑ i, fderiv ℝ u z (spatialDirection i) * Q i z) =
    -(∫ z, w z * fderiv ℝ φ z (0, 1) +
      u z * ∑ i, fderiv ℝ (Q i) z (spatialDirection i))
  rw [integral_add ht.1 hs.1, integral_add ht.2.1 hs.2.1]
  linarith [ht.2.2, hs.2.2]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical

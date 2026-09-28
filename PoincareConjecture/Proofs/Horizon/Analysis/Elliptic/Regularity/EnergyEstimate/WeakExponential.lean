import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.ExponentialTest
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakInequalityLipschitz


noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Poincare.Analysis.Elliptic

open Poincare.Analysis.Sobolev.Weak

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem weakInequality_exponential_test
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u : E → ℝ} {A : ℝ≥0} (hu : LipschitzOnWith A u (closure O))
    {F : Fin d → E → ℝ} {f : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * φ x)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let B := fun x => Real.exp (-u x) *
      ((∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) -
        φ x * ((∑ i, F i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + f x))
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let v := fun x => φ x * Real.exp (-u x)
  obtain ⟨C, hC⟩ := compact_lipschitz_exp_test hOc hu hφ hφc hφO
  have hv0 (x) : 0 ≤ v x := mul_nonneg (hφ0 x) (Real.exp_pos _).le
  have hvc : HasCompactSupport v := hφc.mul_right
  have hvO : tsupport v ⊆ O := tsupport_mul_subset_left.trans hφO
  have hw := weakInequality_of_nonneg_compact_lipschitz
    hO hF hf hweak hC hv0 hvc hvO
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  have hv : MemLp v 2 (volume.restrict O) :=
    (hC.continuous.memLp_of_hasCompactSupport hvc).restrict O
  have hdv (i : Fin d) : MemLp
      (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (memLp_top_fderiv_apply_of_lipschitzOn hO hC.lipschitzOnWith _).mono_exponent le_top
  have hleft : IntegrableOn
      (fun x => ∑ i, F i x * fderiv ℝ v x (EuclideanSpace.single i 1)) O :=
    integrable_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hdv i))
  have hright : IntegrableOn (fun x => f x * v x) O := hf.integrable_mul hv
  have heq : (fun x => (∑ i, F i x * fderiv ℝ v x (EuclideanSpace.single i 1)) -
      f x * v x) =ᵐ[volume.restrict O]
      (fun x => Real.exp (-u x) *
        ((∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) -
          φ x * ((∑ i, F i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + f x))) := by
    filter_upwards [ae_restrict_mem hO.measurableSet,
      ae_restrict_of_ae ((hu.mono subset_closure).ae_differentiableWithinAt_of_mem
        (μ := volume))] with x hx hdx
    have du : DifferentiableAt ℝ u x := (hdx hx).differentiableAt (hO.mem_nhds hx)
    have dv : fderiv ℝ v x = Real.exp (-u x) • fderiv ℝ φ x -
        (φ x * Real.exp (-u x)) • fderiv ℝ u x := by
      change fderiv ℝ (φ * fun y => Real.exp ((-u) y)) x = _
      rw [((hφ.differentiable (by simp) x).hasFDerivAt.mul
        du.hasFDerivAt.neg.exp).fderiv]
      ext w
      simp only [Pi.neg_apply, add_apply, smul_apply, neg_apply, smul_eq_mul, sub_apply]
      ring
    rw [dv]
    simp only [sub_apply, smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    simp_rw [show ∀ i, F i x * (Real.exp (-u x) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      Real.exp (-u x) * (F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) by
        intro i; ring,
      show ∀ i, F i x * (φ x * Real.exp (-u x) *
        fderiv ℝ u x (EuclideanSpace.single i 1)) =
      (φ x * Real.exp (-u x)) * (F i x * fderiv ℝ u x (EuclideanSpace.single i 1)) by
        intro i; ring]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    dsimp only [v]
    ring
  refine ⟨(hleft.sub hright).congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_sub hleft hright]
  exact sub_nonpos.mpr hw

end Poincare.Analysis.Elliptic

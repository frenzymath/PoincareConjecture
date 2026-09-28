import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.KernelBuffer
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakConvolution
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.MollifiedL2Energy

open Set Filter MeasureTheory
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem exists_uniform_mollified_gradient_l2_bound
    {n : ℕ} {U K : Set (Spacetime n)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {u : Spacetime n → ℝ} (hu : LocallyIntegrableOn u U volume)
    {g : Fin n → Spacetime n → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ U →
      (∫ y in U, phi y * g i y) = -(∫ y in U, spatialDeriv i phi y * u y))
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      (∫ y in K, ∑ i, (spatialDeriv i (mollifiedValue u ρ r) y) ^ 2) ≤ B := by
  obtain ⟨ε, hε, hsupport⟩ :=
    exists_uniform_translated_rescaledKernel_support_subset hK hU hKU hρc
  let A : ℝ := ∑ i, (∫ y, ‖ρ y‖) ^ 2 * (∫ y, (g i y) ^ 2)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun y => sq_nonneg _)))
  refine ⟨ε, A + 1, hε, by positivity, ?_⟩
  intro r hr hrε
  have hscale : ContDiff ℝ ∞ (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hderiv (i : Fin n) {y : Spacetime n} (hy : y ∈ K) :
      spatialDeriv i (mollifiedValue u ρ r) y = mollifiedValue (g i) ρ r y := by
    exact fderiv_lebesgueConvolution_eq_weakDerivative hU hu
      (((hg i).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
      (hweak i) hscale hcompact (hsupport r hr hrε y hy)
  have hsq (i : Fin n) : Integrable (fun y => (mollifiedValue (g i) ρ r y) ^ 2) volume :=
    (memLp_lebesgueConvolution (hg i) hscale.continuous hcompact).integrable_sq
  calc
    (∫ y in K, ∑ i, (spatialDeriv i (mollifiedValue u ρ r) y) ^ 2) =
        ∫ y in K, ∑ i, (mollifiedValue (g i) ρ r y) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
      simp_rw [hderiv _ hy]
    _ ≤ ∫ y, ∑ i, (mollifiedValue (g i) ρ r y) ^ 2 :=
      setIntegral_le_integral (integrable_finsetSum _ (fun i _ => hsq i))
        (Eventually.of_forall (fun y => Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    _ = ∑ i, ∫ y, (mollifiedValue (g i) ρ r y) ^ 2 :=
      integral_finsetSum _ (fun i _ => hsq i)
    _ ≤ A := Finset.sum_le_sum (fun i _ =>
      integral_mollifiedValue_sq_le (hg i) hρ.continuous hρc hr)
    _ ≤ A + 1 := by linarith

end Poincare.Analysis.Parabolic.WeakRegularity.Interior

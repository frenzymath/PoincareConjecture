/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/SpectralModeStateNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Analysis.Parabolic.Quasilinear.Heat.SpectralModeL2

/-!
# Scalar identities for the reconstructed heat state

Integrating the assembled coefficient derivatives gives the same explicit
scalar response at every time. Almost-everywhere changes of the forcing do
not change that response. Prefix energy controls the weighted state trace.
-/

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace PoincareMT

/-- The mode is the actual primitive of its equation's time derivative. -/
theorem spectralMode_eq_initial_add_integral_defect
    {lambda c T t : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) (ht : t ∈ uIcc (0 : ℝ) T) :
    spectralMode lambda c f t = c +
      ∫ s in (0 : ℝ)..t, f s - lambda * spectralMode lambda c f s := by
  have hft : IntervalIntegrable f volume 0 t := hf.mono_set (uIcc_subset_uIcc_left ht)
  have hu := absolutelyContinuousOnInterval_spectralMode
    (lambda := lambda) (c := c) hft
  have hprimitive :
      (∫ s in (0 : ℝ)..t, f s - lambda * spectralMode lambda c f s) =
        spectralMode lambda c f t - c := by
    calc
      _ = ∫ s in (0 : ℝ)..t, deriv (spectralMode lambda c f) s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_hasDerivAt_spectralMode (lambda := lambda) (c := c) hft]
          with s hs hmem
        exact (hs (uIoc_subset_uIcc hmem)).deriv.symm
      _ = spectralMode lambda c f t - spectralMode lambda c f 0 :=
        hu.integral_deriv_eq_sub
      _ = _ := by rw [spectralMode_zero]
  linarith

/-- The mode path depends only on the almost-everywhere forcing class. -/
theorem spectralMode_eq_of_ae_eq
    {lambda c T t : ℝ} {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (uIoc (0 : ℝ) T)] g)
    (ht : t ∈ uIcc (0 : ℝ) T) :
    spectralMode lambda c f t = spectralMode lambda c g t := by
  have hsub : uIoc (0 : ℝ) t ⊆ uIoc (0 : ℝ) T :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc_left ht)
  have hfg' := ae_restrict_of_ae_restrict_of_subset hsub hfg
  unfold spectralMode
  apply congrArg (fun z : ℝ => Real.exp (-lambda * t) * (c + z))
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hfg'] with s hs
  rw [hs]

/-- Prefix energy controls the half-generator trace for integrable squares. -/
theorem spectralMode_trace_energy_le_of_integrable
    {lambda c T t : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda)
    (hf : IntervalIntegrable f volume 0 T)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 T)
    (ht : t ∈ Icc (0 : ℝ) T) :
    lambda * spectralMode lambda c f t ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) + lambda * c ^ 2 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  have he := spectralMode_energy_identity_of_integrable
    (lambda := lambda) (c := c) (hf.mono_set hsub) (hf2.mono_set hsub)
  have hD : 0 ≤ ∫ s in (0 : ℝ)..t,
      (f s - lambda * spectralMode lambda c f s) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
  have hA : 0 ≤ ∫ s in (0 : ℝ)..t,
      (lambda * spectralMode lambda c f s) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
  linarith

/-- Arbitrary time-L2 forcing has the same pointwise trace estimate. -/
theorem spectralMode_trace_energy_le_of_memLp
    {lambda c T t : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (ht : t ∈ Icc (0 : ℝ) T) :
    lambda * spectralMode lambda c f t ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) + lambda * c ^ 2 := by
  obtain ⟨hfi, hfi2⟩ := intervalIntegrable_and_sq_of_memLp_two (ht.1.trans ht.2) hf
  exact spectralMode_trace_energy_le_of_integrable hlambda hfi hfi2 ht

end PoincareMT

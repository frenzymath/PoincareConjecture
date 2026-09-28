import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_slice_fst (f : ℝ × ℝ → E) (s u : ℝ)
    (hf : DifferentiableAt ℝ f (s, u)) :
    HasDerivAt (fun r ↦ f (r, u)) (fderiv ℝ f (s, u) (1, 0)) s :=
  hf.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s u))

theorem hasDerivAt_slice_snd (f : ℝ × ℝ → E) (s u : ℝ)
    (hf : DifferentiableAt ℝ f (s, u)) :
    HasDerivAt (fun r ↦ f (s, r)) (fderiv ℝ f (s, u) (0, 1)) u :=
  hf.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u s).prodMk (hasDerivAt_id u))

theorem hasDerivAt_partial_snd_of_initial_fst (f : ℝ × ℝ → E)
    (hf : ContDiffAt ℝ ∞ f (0, 0)) (k : ℝ → E) (w : E)
    (hk : HasDerivAt k w 0)
    (hjet : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun s ↦ f (s, u)) (k u) 0) :
    HasDerivAt (fun s ↦ deriv (fun u ↦ f (s, u)) 0) w 0 := by
  have htwo : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (0, 0) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have htime : HasDerivAt (fun s ↦ fderiv ℝ f (s, 0) (0, 1))
      (fderiv ℝ (fderiv ℝ f) (0, 0) (1, 0) (0, 1)) 0 := by
    simpa only [map_zero, add_zero] using
      (hasDerivAt_slice_fst (fderiv ℝ f) 0 0 hD).clm_apply
        (hasDerivAt_const 0 ((0, 1) : ℝ × ℝ))
  have hparameter : HasDerivAt (fun u ↦ fderiv ℝ f (0, u) (1, 0))
      (fderiv ℝ (fderiv ℝ f) (0, 0) (0, 1) (1, 0)) 0 := by
    simpa only [map_zero, add_zero] using
      (hasDerivAt_slice_snd (fderiv ℝ f) 0 0 hD).clm_apply
        (hasDerivAt_const 0 ((1, 0) : ℝ × ℝ))
  have hnear : ∀ᶠ z in 𝓝 ((0, 0) : ℝ × ℝ), DifferentiableAt ℝ f z :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun z hz ↦ hz.differentiableAt (by simp))
  have hknear : (fun u ↦ fderiv ℝ f (0, u) (1, 0)) =ᶠ[𝓝 (0 : ℝ)] k := by
    filter_upwards [hjet,
      (continuous_const.prodMk continuous_id).continuousAt.eventually hnear] with u hu hd
    exact (hasDerivAt_slice_fst f 0 u hd).unique hu
  have heq := (hparameter.congr_of_eventuallyEq hknear.symm).unique hk
  have hsymm := (hf.isSymmSndFDerivAt (by simpa using htwo)) ((1, 0) : ℝ × ℝ) (0, 1)
  rw [hsymm, heq] at htime
  apply htime.congr_of_eventuallyEq
  filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear]
    with s hs
  exact (hasDerivAt_slice_snd f s 0 hs).deriv

theorem contDiffOn_partial_snd (f : ℝ × ℝ → E) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun s ↦ deriv (fun u ↦ f (s, u)) 0)
      ((fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' U) := by
  have hD := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hcomp : ContDiffOn ℝ ∞ (fun s ↦ fderiv ℝ f (s, 0) (0, 1))
      ((fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' U) :=
    (hD.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun s hs ↦ hs)).clm_apply contDiffOn_const
  apply hcomp.congr
  intro s hs
  exact (hasDerivAt_slice_snd f s 0
    ((hf.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp))).deriv

end PoincareConjecture.Proofs.M09

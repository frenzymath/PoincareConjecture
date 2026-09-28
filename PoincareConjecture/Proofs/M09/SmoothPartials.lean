import PoincareConjecture.Proofs.M09.MixedPartials
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_slice_deriv_fst (f : ℝ × ℝ → E) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ deriv (fun r ↦ f (r, z.2)) z.1) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := ((1, 0) : ℝ × ℝ)))).congr
  intro z hz
  exact (hasDerivAt_slice_fst f z.1 z.2
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv

theorem contDiffOn_slice_deriv_snd (f : ℝ × ℝ → E) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ deriv (fun r ↦ f (z.1, r)) z.2) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))).congr
  intro z hz
  exact (hasDerivAt_slice_snd f z.1 z.2
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv

theorem hasDerivAt_partial_snd_of_fst (f : ℝ × ℝ → E) (s : ℝ)
    (hf : ContDiffAt ℝ ∞ f (s, 0)) (k : ℝ → E) (w : E)
    (hk : HasDerivAt k w 0)
    (hjet : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ f (r, u)) (k u) s) :
    HasDerivAt (fun r ↦ deriv (fun u ↦ f (r, u)) 0) w s := by
  let Y : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
  have htrans : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ (s + z.1, z.2)) (0, 0) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd |>.contDiffAt
  have hF : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ f (s + z.1, z.2)) (0, 0) := by
    have hf' : ContDiffAt ℝ ∞ f (s + 0, 0) := by simpa only [add_zero] using hf
    exact hf'.comp (0, 0) htrans
  have hjet' : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ f (s + r, u)) (k u) 0 := by
    filter_upwards [hjet] with u hu
    simpa only [Function.comp_def, id_eq, one_smul] using hu.scomp_of_eq 0
      ((hasDerivAt_id 0).const_add s) (add_zero s).symm
  have hY : HasDerivAt (fun r ↦ Y (s + r)) w 0 :=
    hasDerivAt_partial_snd_of_initial_fst (fun z : ℝ × ℝ ↦ f (s + z.1, z.2))
      hF k w hk hjet'
  have hback := hY.scomp_of_eq s ((hasDerivAt_id s).sub_const s) (sub_self s).symm
  have hcancel (r : ℝ) : s + (r - s) = r := by ring
  simpa only [Function.comp_def, id_eq, one_smul, hcancel, Y] using hback

noncomputable def timeDerivativePhase (f : ℝ × ℝ → E) (z : ℝ × ℝ) : E × E :=
  (f z, deriv (fun r ↦ f (r, z.2)) z.1)

theorem timeDerivativePhase_contDiffOn (f : ℝ × ℝ → E) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (timeDerivativePhase f) U :=
  hf.prodMk (contDiffOn_slice_deriv_fst f U hU hf)

theorem deriv_timeDerivativePhase_variation (f : ℝ × ℝ → E) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (s : ℝ) (hs : (s, 0) ∈ U) :
    deriv (fun u ↦ timeDerivativePhase f (s, u)) 0 =
      (deriv (fun u ↦ f (s, u)) 0, deriv (fun r ↦ deriv (fun u ↦ f (r, u)) 0) s) := by
  let k : ℝ → E := fun u ↦ deriv (fun r ↦ f (r, u)) s
  have hk : DifferentiableAt ℝ k 0 := by
    have hpartial := (contDiffOn_slice_deriv_fst f U hU hf).contDiffAt (hU.mem_nhds hs)
    exact ((hasDerivAt_slice_snd _ s 0 (hpartial.differentiableAt (by simp))).differentiableAt)
  have hjet : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ f (r, u)) (k u) s := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hs)] with u hu
    exact (hasDerivAt_slice_fst f s u
      ((hf.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp))).differentiableAt.hasDerivAt
  have hmixed := hasDerivAt_partial_snd_of_fst f s (hf.contDiffAt (hU.mem_nhds hs))
    k (deriv k 0) hk.hasDerivAt hjet
  have hu := (hasDerivAt_slice_snd f s 0
    ((hf.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp))).differentiableAt.hasDerivAt
  exact (hu.prodMk (hk.hasDerivAt.congr_deriv hmixed.deriv.symm)).deriv

end PoincareConjecture.Proofs.M09

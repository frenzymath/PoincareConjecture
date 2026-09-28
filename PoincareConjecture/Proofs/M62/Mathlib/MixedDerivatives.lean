import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter Topology
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false in

theorem ContDiffAt.exists_hasDerivAt_mixed
    {K E : Type*} [NontriviallyNormedField K] [IsRCLikeNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {f : K × K → E} {p : K × K} (hf : ContDiffAt K 2 f p) :
    ∃ k : E,
      HasDerivAt (fun u ↦ deriv (fun s ↦ f (s, u)) p.1) k p.2 ∧
      HasDerivAt (fun s ↦ deriv (fun u ↦ f (s, u)) p.2) k p.1 := by
  have hfd : DifferentiableAt K (fderiv K f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hnear := hf.eventually (by norm_num)
  let k := fderiv K (fderiv K f) p (0, 1) (1, 0)
  refine ⟨k, ?_, ?_⟩
  · have h := (hfd.hasFDerivAt.comp_hasDerivAt (f := fun u : K ↦ (p.1, u)) p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).clm_apply
        (hasDerivAt_const p.2 ((1 : K), (0 : K)))
    have hd : HasDerivAt (fun u ↦ fderiv K f (p.1, u) (1, 0)) k p.2 := by
      simpa only [Function.comp_def, id_eq, k, map_zero, add_zero] using h
    apply hd.congr_of_eventuallyEq
    have hgerm : ∀ᶠ u in 𝓝 p.2, ContDiffAt K 2 f (p.1, u) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually hnear
    filter_upwards [hgerm] with u hu
    exact ((hu.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt
      (f := fun s : K ↦ (s, u)) p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 u))).deriv
  · have h := (hfd.hasFDerivAt.comp_hasDerivAt (f := fun s : K ↦ (s, p.2)) p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).clm_apply
        (hasDerivAt_const p.1 ((0 : K), (1 : K)))
    have hsym := (hf.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField])) (1, 0) (0, 1)
    have hd : HasDerivAt (fun s ↦ fderiv K f (s, p.2) (0, 1)) k p.1 := by
      simpa only [Function.comp_def, id_eq, k, map_zero, add_zero, hsym] using h
    apply hd.congr_of_eventuallyEq
    have hgerm : ∀ᶠ s in 𝓝 p.1, ContDiffAt K 2 f (s, p.2) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually hnear
    filter_upwards [hgerm] with s hs
    exact ((hs.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt
      (f := fun u : K ↦ (s, u)) p.2
      ((hasDerivAt_const p.2 s).prodMk (hasDerivAt_id p.2))).deriv

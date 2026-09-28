import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial
import Mathlib.Analysis.Calculus.FDeriv.Partial

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

noncomputable def profileTimePartial (f : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  fderiv ℝ (Function.uncurry f) (t, r) (1, 0)

noncomputable def profileRadiusPartial (f : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  fderiv ℝ (Function.uncurry f) (t, r) (0, 1)

theorem profileFamily_slice_contDiff {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) : ContDiff ℝ ∞ (f t) := by
  rw [← contDiffOn_univ]
  exact hf.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun _ _ => ⟨ht, mem_univ _⟩)

theorem profileTimePartial_contDiffOn {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (profileTimePartial f)) (J ×ˢ univ) :=
  (hf.fderiv_of_isOpen (hJ.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

theorem profileRadiusPartial_contDiffOn {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (profileRadiusPartial f)) (J ×ˢ univ) :=
  (hf.fderiv_of_isOpen (hJ.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

theorem profileFamily_hasDerivAt_time {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) (r : ℝ) :
    HasDerivAt (fun s => f s r) (profileTimePartial f t r) t := by
  have hc : ContDiffAt ℝ ∞ (Function.uncurry f) (t, r) :=
    hf.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ r⟩)
  have h := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
  exact h

theorem profileFamily_hasDerivAt_radius {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) (r : ℝ) :
    HasDerivAt (f t) (profileRadiusPartial f t r) r := by
  have hc : ContDiffAt ℝ ∞ (Function.uncurry f) (t, r) :=
    hf.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ r⟩)
  have h := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))
  exact h

theorem profileRadiusPartial_eq_deriv {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) : profileRadiusPartial f t = deriv (f t) :=
  funext (fun r => (profileFamily_hasDerivAt_radius hJ hf ht r).deriv.symm)

theorem profileTimePartial_even {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    (he : ∀ t ∈ J, Function.Even (f t)) {t : ℝ} (ht : t ∈ J) :
    Function.Even (profileTimePartial f t) := by
  intro r
  have hminus := profileFamily_hasDerivAt_time hJ hf ht (-r)
  have hplus : HasDerivAt (fun s => f s (-r)) (profileTimePartial f t r) t := by
    apply (profileFamily_hasDerivAt_time hJ hf ht r).congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact he s hs r
  exact hminus.unique hplus

end PoincareConjecture.M35.RadialGauge

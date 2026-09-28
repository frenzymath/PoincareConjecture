import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false

open scoped Manifold

variable {E H M V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]


set_option backward.isDefEq.respectTransparency false in


theorem moving_linearMap_comp_hasDerivAt {f : M → V →L[ℝ] W}
    {γ : ℝ → M} {v : ℝ → V} {s : ℝ} {k : V}
    (hf : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] W) f (γ s))
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ s) (hv : HasDerivAt v k s) :
    HasDerivAt (fun r => f (γ r) (v r))
      (mvfderiv I (fun p => f p (v s)) (γ s) (mfderiv 𝓘(ℝ) I γ s (1 : ℝ)) +
        f (γ s) k) s := by
  have hc := (hf.comp s hγ).differentiableAt.hasDerivAt
  have hconst := hc.clm_apply (hasDerivAt_const s (v s))
  have hfixed := ((hf.clm_apply (mdifferentiableAt_const (c := v s))).hasMFDerivAt.comp s
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun r => f (γ r) (v s))
    (mvfderiv I (fun p => f p (v s)) (γ s) (mfderiv 𝓘(ℝ) I γ s (1 : ℝ))) s at hfixed
  have hd : deriv (f ∘ γ) s (v s) =
      mvfderiv I (fun p => f p (v s)) (γ s) (mfderiv 𝓘(ℝ) I γ s (1 : ℝ)) := by
    simpa only [map_zero, add_zero] using hconst.unique hfixed
  convert! hc.clm_apply hv using 1
  exact congrArg (fun w => w + f (γ s) k) hd.symm

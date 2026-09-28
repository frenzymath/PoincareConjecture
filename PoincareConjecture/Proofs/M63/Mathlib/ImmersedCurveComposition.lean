import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

universe u v

namespace PoincareConjecture.M63

variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffAt_of_comp_immersed_curve
    {k : WithTop ℕ∞} (hk : k ≠ 0) {phi : A → ℝ} {f : ℝ → E} {x : A}
    (hphi : ContinuousAt phi x) (hf : ContDiffAt ℝ k f (phi x))
    (hder : deriv f (phi x) ≠ 0) (hcomp : ContDiffAt ℝ k (f ∘ phi) x) :
    ContDiffAt ℝ k phi x := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ (deriv f (phi x))
  let g : ℝ → ℝ := fun y => ell (f y)
  have hg : ContDiffAt ℝ k g (phi x) := ell.contDiff.contDiffAt.comp (phi x) hf
  have hd : HasDerivAt g (ell (deriv f (phi x))) (phi x) :=
    ell.hasFDerivAt.comp_hasDerivAt (phi x) ((hf.differentiableAt hk).hasDerivAt)
  have hne : ell (deriv f (phi x)) ≠ 0 := inner_self_ne_zero.mpr hder
  have hge := hd.hasFDerivAt_equiv hne
  have hscalar : ContDiffAt ℝ k (fun z => g (phi z)) x :=
    ell.contDiff.contDiffAt.comp x hcomp
  have hleft : ∀ᶠ y in 𝓝 (phi x), hg.localInverse hge hk (g y) = y :=
    (hg.hasStrictFDerivAt' hge hk).eventually_left_inverse
  have heq : (fun z => hg.localInverse hge hk (g (phi z))) =ᶠ[𝓝 x] phi :=
    hphi.eventually hleft
  exact ((hg.to_localInverse hge hk).comp x hscalar).congr_of_eventuallyEq heq.symm

end PoincareConjecture.M63

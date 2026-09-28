import PoincareConjecture.Proofs.M63.Mathlib.ImmersedCurveComposition
import Mathlib.Analysis.Calculus.ContDiff.RCLike






noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology ContDiff NNReal

namespace PoincareConjecture

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem m64ContDiffWithinAt_of_comp_immersed_curve
    {k : WithTop ℕ∞} (hk : k ≠ 0) {phi : A → ℝ} {f : ℝ → E}
    {S : Set A} {x : A} (hx : x ∈ S)
    (hphi : ContinuousWithinAt phi S x) (hf : ContDiffAt ℝ k f (phi x))
    (hder : deriv f (phi x) ≠ 0) (hcomp : ContDiffWithinAt ℝ k (f ∘ phi) S x) :
    ContDiffWithinAt ℝ k phi S x := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ (deriv f (phi x))
  let g : ℝ → ℝ := fun y => ell (f y)
  have hg : ContDiffAt ℝ k g (phi x) := ell.contDiff.contDiffAt.comp (phi x) hf
  have hd : HasDerivAt g (ell (deriv f (phi x))) (phi x) :=
    ell.hasFDerivAt.comp_hasDerivAt (phi x) ((hf.differentiableAt hk).hasDerivAt)
  have hne : ell (deriv f (phi x)) ≠ 0 := inner_self_ne_zero.mpr hder
  have hge := hd.hasFDerivAt_equiv hne
  have hscalar : ContDiffWithinAt ℝ k (fun z => g (phi z)) S x :=
    ell.contDiff.contDiffAt.comp_contDiffWithinAt x hcomp
  have hleft : ∀ᶠ y in 𝓝 (phi x), hg.localInverse hge hk (g y) = y :=
    (hg.hasStrictFDerivAt' hge hk).eventually_left_inverse
  have heq : (fun z => hg.localInverse hge hk (g (phi z))) =ᶠ[𝓝[S] x] phi :=
    hphi.eventually hleft
  have hregular := (hg.to_localInverse hge hk).comp_contDiffWithinAt x hscalar
  exact hregular.congr_of_eventuallyEq_of_mem heq.symm hx




theorem m64Label_lipschitzOn_of_regular_trace
    {phi : ℝ → ℝ} {f : ℝ → E} {a b : ℝ}
    (hphi : ContinuousOn phi (Icc a b)) (hf : ContDiff ℝ 1 f)
    (hder : ∀ t, deriv f t ≠ 0) (hcomp : ContDiffOn ℝ 1 (f ∘ phi) (Icc a b)) :
    ∃ K : ℝ≥0, LipschitzOnWith K phi (Icc a b) := by
  have hC1 : ContDiffOn ℝ 1 phi (Icc a b) := fun x hx =>
    m64ContDiffWithinAt_of_comp_immersed_curve one_ne_zero hx (hphi x hx)
      hf.contDiffAt (hder (phi x)) (hcomp x hx)
  exact hC1.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc

end PoincareConjecture

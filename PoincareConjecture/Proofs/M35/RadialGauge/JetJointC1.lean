import PoincareConjecture.Proofs.M35.RadialGauge.JointC1
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_jets_joint_c1_of_time_equation
    {u H : ℝ → E → F} {a b : ℝ}
    (hs : ∀ t ∈ Icc a b, ContDiff ℝ ∞ (u t))
    (huj : ∀ j : ℕ, Continuous
      (fun p : Icc a b × E => iteratedFDeriv ℝ j (u p.1.1) p.2))
    (hHj : ∀ j : ℕ, Continuous
      (fun p : Icc a b × E => iteratedFDeriv ℝ j (H p.1.1) p.2))
    (htime : ∀ j t, t ∈ Ioo a b → ∀ x,
      HasDerivAt (fun s => iteratedFDeriv ℝ j (u s) x)
        (iteratedFDeriv ℝ j (H t) x) t) (j : ℕ) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => iteratedFDeriv ℝ j (u p.1) p.2)
      (Ioo a b ×ˢ univ) := by
  have hspace (t : ℝ) (ht : t ∈ Icc a b) :
      Differentiable ℝ (iteratedFDeriv ℝ j (u t)) := by
    intro x
    exact (hs t ht).contDiffAt.differentiableAt_iteratedFDeriv
      (show (j : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
  have hdc : Continuous
      (fun p : Icc a b × E => fderiv ℝ (iteratedFDeriv ℝ j (u p.1.1)) p.2) := by
    have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).continuous.comp
      (huj (j + 1))
    simpa only [fderiv_iteratedFDeriv, Function.comp_def] using h
  exact joint_contDiffOn_one_of_slab_partials hspace (htime j) (hHj j) hdc

end PoincareConjecture.M35.RadialGauge

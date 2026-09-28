import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationVelocity
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem slice_jet_contDiffOn (f : P × (ℝ × ℝ) → LoopAmbient)
    (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun z => iteratedFDeriv ℝ j (fun w => f (z.1, w)) z.2) U := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) LoopAmbient).symm.contDiff.comp_contDiffOn hf
  | succ j hj =>
    intro z hz
    have hunc : ContDiffAt ℝ ∞
        (fun w : (P × (ℝ × ℝ)) × (ℝ × ℝ) =>
          iteratedFDeriv ℝ j (fun x => f (w.1.1, x)) w.2) (z, z.2) :=
      (hj.contDiffAt (hU.mem_nhds hz)).comp (z, z.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun w : P × (ℝ × ℝ) =>
        fderiv ℝ (fun x : ℝ × ℝ => iteratedFDeriv ℝ j (fun y => f (w.1, y)) x) w.2) z :=
      ContDiffAt.fderiv
        (f := fun w : P × (ℝ × ℝ) => fun x : ℝ × ℝ =>
          iteratedFDeriv ℝ j (fun y => f (w.1, y)) x)
        (g := fun w : P × (ℝ × ℝ) => w.2) hunc contDiffAt_snd (by simp)
    have h := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) => ℝ × ℝ) LoopAmbient).symm.contDiff.contDiffAt.comp z hd
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using h.contDiffWithinAt

end PoincareConjecture.M65Perturbation

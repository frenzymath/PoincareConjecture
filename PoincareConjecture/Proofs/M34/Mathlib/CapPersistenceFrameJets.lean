import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds
import Mathlib.Analysis.Normed.Operator.Bilinear










set_option autoImplicit false

open scoped ContDiff BigOperators
open Poincare.Analysis.Calculus




theorem norm_iteratedFDeriv_succ_le_of_frame
    {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]
    (e : ι → E) (ell : ι → E →L[𝕜] 𝕜)
    (hframe : ∀ v : E, ∑ i, ell i v • e i = v)
    {f : E → F} {x : E} (m : ℕ) (hf : ContDiffAt 𝕜 (m + 1) f x) :
    ‖iteratedFDeriv 𝕜 (m + 1) f x‖ ≤
      ∑ i, ‖ContinuousLinearMap.smulRightL 𝕜 E F (ell i)‖ *
        ‖iteratedFDeriv 𝕜 m (fun y => fderiv 𝕜 f y (e i)) x‖ := by
  classical
  let L (i : ι) : F →L[𝕜] E →L[𝕜] F :=
    ContinuousLinearMap.smulRightL 𝕜 E F (ell i)
  have heq : fderiv 𝕜 f = fun y => ∑ i, L i (fderiv 𝕜 f y (e i)) := by
    funext y
    ext v
    rw [sum_apply]
    change fderiv 𝕜 f y v = ∑ i, ell i v • fderiv 𝕜 f y (e i)
    calc
      _ = fderiv 𝕜 f y (∑ i, ell i v • e i) := congrArg (fderiv 𝕜 f y) (hframe v).symm
      _ = _ := by simp only [map_sum, map_smul]
  have hs (i : ι) : ContDiffAt 𝕜 m (fun y => fderiv 𝕜 f y (e i)) x :=
    (hf.fderiv_right (m := (m : ℕ∞ω)) (by simp)).clm_apply contDiffAt_const
  calc
    _ = ‖iteratedFDeriv 𝕜 m (fderiv 𝕜 f) x‖ := norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv 𝕜 m (fun y => ∑ i, L i (fderiv 𝕜 f y (e i))) x‖ :=
      congrArg (fun h => ‖iteratedFDeriv 𝕜 m h x‖) heq
    _ ≤ ∑ i, ‖iteratedFDeriv 𝕜 m (fun y => L i (fderiv 𝕜 f y (e i))) x‖ :=
      norm_iteratedFDeriv_sum_le_of_contDiffAt Finset.univ m
        (fun i _ => (L i).contDiff.contDiffAt.comp x (hs i))
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      (L i).norm_iteratedFDeriv_comp_left (hs i) (le_refl _)

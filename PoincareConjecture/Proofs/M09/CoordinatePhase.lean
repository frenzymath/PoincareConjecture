import PoincareConjecture.Proofs.M09.PositiveForm
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def coordinatePhaseCovector (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (v : E) : E →L[ℝ] ℝ :=
  (2 * z.1 ^ 2) • (fderiv ℝ R z).comp (ContinuousLinearMap.inr ℝ ℝ E) -
    (fderiv ℝ G z (1, 0)) v - (fderiv ℝ G z (0, v)) v +
    (1 / 2 : ℝ) •
      (((ContinuousLinearMap.apply ℝ ℝ v).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)).comp
        ((fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ ℝ E)))

noncomputable def regularizedCoordinatePhase (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (q : ℝ × (E × E)) : E × E :=
  (q.2.2, (G (q.1, q.2.1)).inverse (coordinatePhaseCovector G R (q.1, q.2.1) q.2.2))

theorem regularizedCoordinatePhase_smooth (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (U : Set (ℝ × E)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (regularizedCoordinatePhase G R)
      {q : ℝ × (E × E) | (q.1, q.2.1) ∈ U} := by
  let W : Set (ℝ × (E × E)) := {q | (q.1, q.2.1) ∈ U}
  let P : ℝ × (E × E) → ℝ × E := fun q ↦ (q.1, q.2.1)
  let V : ℝ × (E × E) → E := fun q ↦ q.2.2
  have hP : ContDiff ℝ ∞ P := contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hV : ContDiff ℝ ∞ V := contDiff_snd.comp contDiff_snd
  have hDG : ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ G (P q)) W :=
    (hG.fderiv_of_isOpen hU (by simp)).comp hP.contDiffOn (fun _ h ↦ h)
  have hDR : ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ R (P q)) W :=
    (hR.fderiv_of_isOpen hU (by simp)).comp hP.contDiffOn (fun _ h ↦ h)
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) U := by
    intro z hz
    exact (positiveForm_isInvertible (G z) (hpos z hz)).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt z (hG z hz)
  have hRsp : ContDiffOn ℝ ∞
      (fun q ↦ (fderiv ℝ R (P q)).comp (ContinuousLinearMap.inr ℝ ℝ E)) W :=
    hDR.clm_comp contDiffOn_const
  have hTime : ContDiffOn ℝ ∞ (fun q ↦ (fderiv ℝ G (P q) (1, 0)) (V q)) W :=
    (hDG.clm_apply contDiffOn_const).clm_apply hV.contDiffOn
  have hSpace : ContDiffOn ℝ ∞
      (fun q ↦ (fderiv ℝ G (P q) (0, V q)) (V q)) W :=
    (hDG.clm_apply (contDiffOn_const.prodMk hV.contDiffOn)).clm_apply hV.contDiffOn
  have hEval : ContDiffOn ℝ ∞
      (fun q ↦ (ContinuousLinearMap.apply ℝ ℝ (V q)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (V q))) W :=
    ((ContinuousLinearMap.apply ℝ ℝ).contDiff.comp hV).contDiffOn.clm_comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).contDiff.comp hV).contDiffOn
  have hQuad : ContDiffOn ℝ ∞
      (fun q ↦ ((ContinuousLinearMap.apply ℝ ℝ (V q)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (V q))).comp
        ((fderiv ℝ G (P q)).comp (ContinuousLinearMap.inr ℝ ℝ E))) W :=
    hEval.clm_comp (hDG.clm_comp contDiffOn_const)
  have hC : ContDiffOn ℝ ∞ (fun q ↦ coordinatePhaseCovector G R (P q) (V q)) W :=
    ((((contDiffOn_const.mul (contDiffOn_fst.pow 2)).smul hRsp).sub hTime).sub hSpace).add
      ((contDiffOn_const (c := (1 / 2 : ℝ))).smul hQuad)
  exact hV.contDiffOn.prodMk
    ((hInv.comp hP.contDiffOn (fun _ h ↦ h)).clm_apply hC)

theorem regularizedCoordinatePhase_pairing (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (v w : E) :
    G z (regularizedCoordinatePhase G R (z.1, (z.2, v))).2 w =
      2 * z.1 ^ 2 * fderiv ℝ R z (0, w) - fderiv ℝ G z (1, 0) v w -
        fderiv ℝ G z (0, v) v w + (1 / 2 : ℝ) * fderiv ℝ G z (0, w) v v := by
  change G z ((G z).inverse (coordinatePhaseCovector G R z v)) w = _
  rw [(positiveForm_isInvertible (G z) hpos).self_apply_inverse]
  rfl

end PoincareConjecture.Proofs.M09

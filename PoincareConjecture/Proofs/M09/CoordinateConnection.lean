import PoincareConjecture.Proofs.M09.PositiveForm
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def coordinateConnectionCovector (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ((fderiv ℝ G z (0, v)) w + (fderiv ℝ G z (0, w)) v -
    (((ContinuousLinearMap.apply ℝ ℝ w).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)).comp
        ((fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ ℝ E))))

noncomputable def coordinateConnection (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w : E) : E :=
  (G z).inverse (coordinateConnectionCovector G z v w)

theorem coordinateConnection_pairing (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (v w u : E) :
    G z (coordinateConnection G z v w) u =
      (1 / 2 : ℝ) * (fderiv ℝ G z (0, v) w u +
        fderiv ℝ G z (0, w) v u - fderiv ℝ G z (0, u) v w) := by
  unfold coordinateConnection
  rw [(positiveForm_isInvertible (G z) hpos).self_apply_inverse]
  rfl

theorem coordinateConnection_smooth (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦
      coordinateConnection G q.1 q.2.1 q.2.2) {q | q.1 ∈ U} := by
  let S : Set ((ℝ × E) × (E × E)) := {q | q.1 ∈ U}
  have hDG : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ fderiv ℝ G q.1) S :=
    (hG.fderiv_of_isOpen hU (by simp)).comp contDiffOn_fst (fun q hq ↦ hq)
  have hv : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ q.2.1) S :=
    contDiffOn_fst.comp contDiffOn_snd (fun _ _ ↦ Set.mem_univ _)
  have hw : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ q.2.2) S :=
    contDiffOn_snd.comp contDiffOn_snd (fun _ _ ↦ Set.mem_univ _)
  have hfirst := (hDG.clm_apply ((contDiffOn_const (c := (0 : ℝ))).prodMk hv)).clm_apply hw
  have hsecond := (hDG.clm_apply ((contDiffOn_const (c := (0 : ℝ))).prodMk hw)).clm_apply hv
  have heval : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × (E × E) ↦ (ContinuousLinearMap.apply ℝ ℝ q.2.2).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) q.2.1)) S :=
    ((ContinuousLinearMap.apply ℝ ℝ).contDiff.contDiffOn.comp hw (fun _ _ ↦ Set.mem_univ _)).clm_comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).contDiff.contDiffOn.comp hv
        (fun _ _ ↦ Set.mem_univ _))
  have hlast := heval.clm_comp (hDG.clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E)))
  have hC : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × (E × E) ↦ coordinateConnectionCovector G q.1 q.2.1 q.2.2) S :=
    (contDiffOn_const (c := (1 / 2 : ℝ))).smul ((hfirst.add hsecond).sub hlast)
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) U := by
    intro z hz
    exact (positiveForm_isInvertible (G z) (hpos z hz)).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt z (hG z hz)
  exact (hInv.comp contDiffOn_fst (fun _ h ↦ h)).clm_apply hC

end PoincareConjecture.Proofs.M09

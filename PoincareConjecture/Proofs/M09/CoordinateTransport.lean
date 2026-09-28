import PoincareConjecture.Proofs.M09.CoordinateCompatibility
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def coordinateTransportOperator
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E) (a : E) : E →L[ℝ] E :=
  -coordinateConnectionBilinear G z a -
    (1 / 2 : ℝ) • ((G z).inverse.comp (fderiv ℝ G z (1, 0)))

theorem coordinateTransportOperator_contDiffOn
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × E) × E ↦ coordinateTransportOperator G q.1 q.2)
      (U ×ˢ Set.univ) := by
  have hC : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × E ↦ coordinateConnectionBilinear G q.1) (U ×ˢ Set.univ) :=
    (coordinateConnectionBilinear_contDiffOn G U hU hG hpos).comp
      contDiffOn_fst (fun q hq ↦ hq.1)
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) U := by
    intro z hz
    exact (positiveForm_isInvertible (G z) (hpos z hz)).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt z (hG z hz)
  have hTime : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ G z (1, 0)) U :=
    (hG.fderiv_of_isOpen hU (by simp)).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : E))))
  have hRest : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × E ↦ (G q.1).inverse.comp (fderiv ℝ G q.1 (1, 0)))
      (U ×ˢ Set.univ) :=
    (hInv.clm_comp hTime).comp contDiffOn_fst (fun q hq ↦ hq.1)
  exact (hC.clm_apply contDiffOn_snd).neg.sub
    ((contDiffOn_const (c := (1 / 2 : ℝ))).smul hRest)

theorem coordinateTransportOperator_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (a v w : E) :
    G z (coordinateTransportOperator G z a v) w =
      -G z (coordinateConnection G z a v) w - (1 / 2 : ℝ) * fderiv ℝ G z (1, 0) v w := by
  simp only [coordinateTransportOperator, sub_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_neg, map_smul, smul_eq_mul,
    coordinateConnectionBilinear_apply]
  rw [(positiveForm_isInvertible (G z) hpos).self_apply_inverse]

theorem coordinateTransportOperator_metric_identity
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (a v w : E) :
    fderiv ℝ G z (1, a) v w + G z (coordinateTransportOperator G z a v) w +
      G z v (coordinateTransportOperator G z a w) = 0 := by
  have hsplit : ((1 : ℝ), a) = (1, (0 : E)) + (0, a) := by simp
  have hpoint := hsym.self_of_nhds
  rw [hsplit, map_add, add_apply, add_apply,
    hpoint v (coordinateTransportOperator G z a w),
    coordinateTransportOperator_pairing G z hpos a v w,
    coordinateTransportOperator_pairing G z hpos a w v,
    fderiv_bilinear_symm G z hG hsym (1, 0) w v,
    coordinateConnection_compatible G z hG hsym hpos a v w,
    hpoint v (coordinateConnection G z a w)]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_coordinateTransport_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (y u v : ℝ → E) (t : ℝ) (a : E)
    (hG : DifferentiableAt ℝ G (t, y t))
    (hsym : ∀ᶠ q in 𝓝 (t, y t), ∀ v w, G q v w = G q w v)
    (hpos : ∀ w : E, w ≠ 0 → 0 < G (t, y t) w w)
    (hy : HasDerivAt y a t)
    (hu : HasDerivAt u (coordinateTransportOperator G (t, y t) a (u t)) t)
    (hv : HasDerivAt v (coordinateTransportOperator G (t, y t) a (v t)) t) :
    HasDerivAt (fun r ↦ G (r, y r) (u r) (v r)) 0 t := by
  have hbase : HasDerivAt (fun r ↦ (r, y r)) (1, a) t := (hasDerivAt_id t).prodMk hy
  have hmetric := hG.hasFDerivAt.comp_hasDerivAt t hbase
  have h := (hmetric.clm_apply hu).clm_apply hv
  apply h.congr_deriv
  simpa only [add_apply, Function.comp_apply] using
    coordinateTransportOperator_metric_identity G (t, y t) hG hsym hpos a (u t) (v t)

end PoincareConjecture.Proofs.M09

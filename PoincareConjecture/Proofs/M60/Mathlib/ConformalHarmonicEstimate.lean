import PoincareConjecture.Proofs.M60.Mathlib.MapMetricBochner
import PoincareConjecture.Proofs.M60.Mathlib.DifferentiatedConformality
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Metric

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open ConnectionVariation CoordinateExponential

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conformal_harmonic_map_estimate
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {a : P → ℝ} {O : Set P} {p : P}
    (hO : IsOpen O) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hG : ContDiffOn ℝ ∞ G O)
    (hΓ : ∀ q ∈ O, ContDiffAt ℝ ∞ Γ (u q))
    (hcompat : ∀ q ∈ O, ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun r => G r b c) q v =
        G q (Γ (u q) (fderiv ℝ u q v) b) c +
          G q b (Γ (u q) (fderiv ℝ u q v) c))
    (hGsymm : ∀ b c : E, G p b c = G p c b)
    (hGnonneg : ∀ v, 0 ≤ G p v v)
    (hΓsymm : ∀ q ∈ O, ∀ b c, Γ (u q) b c = Γ (u q) c b)
    (hharm : ∀ q ∈ O,
      covDerivAlong Γ u (fun r => fderiv ℝ u r d) d q +
        covDerivAlong Γ u (fun r => fderiv ℝ u r e) e q = 0)
    (hdd : ∀ q ∈ O, G q (fderiv ℝ u q d) (fderiv ℝ u q d) = a q)
    (hee : ∀ q ∈ O, G q (fderiv ℝ u q e) (fderiv ℝ u q e) = a q)
    (hde : ∀ q ∈ O, G q (fderiv ℝ u q d) (fderiv ℝ u q e) = 0)
    (ha : 0 < a p) :
    ((fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2) / a p -
      2 * G p (christoffelCurvature Γ (u p) (fderiv ℝ u p d)
        (fderiv ℝ u p e) (fderiv ℝ u p e)) (fderiv ℝ u p d) ≤
      fderiv ℝ (fun q => fderiv ℝ a q d) p d +
        fderiv ℝ (fun q => fderiv ℝ a q e) p e := by
  have hub := hu.contDiffAt (hO.mem_nhds hp)
  have hdu (v : P) : ContDiffAt ℝ ∞ (fun q => fderiv ℝ u q v) p :=
    (hub.fderiv_right (by simp)).clm_apply contDiffAt_const
  have htor := covDerivAlong_fderiv_symm
    (hub.of_le (WithTop.coe_le_coe.mpr le_top)) (hΓsymm p hp) d e
  have hgrad := conformal_pairing_gradient_bound
    (Γ := mapConnectionCoefficients Γ u) d e
    ((hG.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
    ((hdu d).differentiableAt (by simp)) ((hdu e).differentiableAt (by simp))
    (hcompat p hp) hGsymm hGnonneg
    (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hdd q hq)
    (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hee q hq)
    (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hde q hq) htor ha
  simp only [covariantDerivative_mapConnectionCoefficients] at hgrad
  have hb := harmonic_map_metric_bochner hO hp d e hu hG hΓ hcompat
    hGsymm hΓsymm hharm hdd
  have hskew : christoffelCurvature Γ (u p) (fderiv ℝ u p e)
      (fderiv ℝ u p d) (fderiv ℝ u p e) =
      -christoffelCurvature Γ (u p) (fderiv ℝ u p d)
        (fderiv ℝ u p e) (fderiv ℝ u p e) := by
    simp only [christoffelCurvature]
    abel
  rw [hskew, map_neg, neg_apply] at hb
  linarith

variable [CompleteSpace E]

theorem christoffel_conformal_harmonic_estimate
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {u : P → E} {a : P → ℝ}
    {O : Set P} {V : Set E} {p : P}
    (hO : IsOpen O) (hV : IsOpen V) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hB : ContDiffOn ℝ ∞ B V)
    (hmap : MapsTo u O V)
    (hBsymm : ∀ x ∈ V, ∀ b c, B x b c = B x c b)
    (hinv : ∀ x ∈ V, (B x).IsInvertible)
    (hnonneg : ∀ v, 0 ≤ B (u p) v v)
    (hharm : ∀ q ∈ O,
      covDerivAlong (christoffelBilinear B) u (fun r => fderiv ℝ u r d) d q +
        covDerivAlong (christoffelBilinear B) u (fun r => fderiv ℝ u r e) e q = 0)
    (hdd : ∀ q ∈ O, B (u q) (fderiv ℝ u q d) (fderiv ℝ u q d) = a q)
    (hee : ∀ q ∈ O, B (u q) (fderiv ℝ u q e) (fderiv ℝ u q e) = a q)
    (hde : ∀ q ∈ O, B (u q) (fderiv ℝ u q d) (fderiv ℝ u q e) = 0)
    (ha : 0 < a p) :
    ((fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2) / a p -
      2 * B (u p) (coordinateCurvature B (u p) (fderiv ℝ u p d)
        (fderiv ℝ u p e) (fderiv ℝ u p e)) (fderiv ℝ u p d) ≤
      fderiv ℝ (fun q => fderiv ℝ a q d) p d +
        fderiv ℝ (fun q => fderiv ℝ a q e) p e := by
  have hBq (q : P) (hq : q ∈ O) : ContDiffAt ℝ ∞ B (u q) :=
    hB.contDiffAt (hV.mem_nhds (hmap hq))
  have hsymq (q : P) (hq : q ∈ O) :
      ∀ᶠ x in 𝓝 (u q), ∀ b c, B x b c = B x c b :=
    Filter.Eventually.mono (hV.mem_nhds (hmap hq)) fun x hx => hBsymm x hx
  have hΓ (q : P) (hq : q ∈ O) : ContDiffAt ℝ ∞ (christoffelBilinear B) (u q) :=
    contDiffAt_christoffelBilinear (hBq q hq) (hinv _ (hmap hq))
  have hcompat (q : P) (hq : q ∈ O) (v : P) (b c : E) :
      fderiv ℝ (fun r => B (u r) b c) q v =
        B (u q) (christoffelBilinear B (u q) (fderiv ℝ u q v) b) c +
          B (u q) b (christoffelBilinear B (u q) (fderiv ℝ u q v) c) := by
    have hdB := (hBq q hq).differentiableAt (by simp)
    have hdu := (hu.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
    have hd := ((hdB.hasFDerivAt.comp q hdu.hasFDerivAt).clm_apply
      (hasFDerivAt_const b q)).clm_apply (hasFDerivAt_const c q)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact fderiv_metric_eq_christoffel hdB (hinv _ (hmap hq)) (hsymq q hq) b c _
  rw [coordinateCurvature_eq_christoffelCurvature ((hΓ p hp).differentiableAt (by simp))]
  exact conformal_harmonic_map_estimate hO hp d e hu (hB.comp hu hmap) hΓ hcompat
    (hBsymm _ (hmap hp)) hnonneg
    (fun q hq => christoffelBilinear_symm ((hBq q hq).differentiableAt (by simp))
      (hsymq q hq)) hharm hdd hee hde ha

end PoincareConjecture.M60

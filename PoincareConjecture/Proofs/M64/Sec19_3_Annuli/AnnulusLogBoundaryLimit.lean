import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLogRegularization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

theorem m64Annulus_log_normal_trace_tendsto_on_slice
    {a : LoopPlane → ℝ} {O : Set LoopPlane} (hO : IsOpen O)
    (ha : ContDiffOn ℝ ∞ a O) (s : ℝ)
    (hpoint : ∀ x ∈ Icc (0 : ℝ) curvePeriod, annulusPoint x s ∈ O)
    (hpos : ∀ x ∈ Icc (0 : ℝ) curvePeriod, 0 < a (annulusPoint x s)) :
    Tendsto (fun m : ℕ => ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log (a q + 1 / ((m : ℝ) + 1)))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) atTop
      (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ a (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) /
          a (annulusPoint x s))) := by
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let F := fun x : ℝ => a (annulusPoint x s)
  let G := fun x : ℝ => fderiv ℝ a (annulusPoint x s) b1 / F x
  have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
    unfold annulusPoint
    fun_prop
  have hF : ContinuousOn F (Icc (0 : ℝ) curvePeriod) :=
    ha.continuousOn.comp hcurve.continuousOn hpoint
  have hD : ContinuousOn (fun x => fderiv ℝ a (annulusPoint x s) b1)
      (Icc (0 : ℝ) curvePeriod) :=
    ((ha.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn.comp
      hcurve.continuousOn hpoint
  have hG : IntegrableOn G (Icc (0 : ℝ) curvePeriod) volume :=
    (hD.div hF (fun x hx => (hpos x hx).ne')).integrableOn_compact isCompact_Icc
  have hposae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), 0 < F x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hpos x hx
  have hlim := M60.tendsto_integral_regularized_ratio
    (hF.aemeasurable measurableSet_Icc) hposae hG
  convert hlim using 1
  funext m
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hepsilon : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hden : 0 < a (annulusPoint x s) + 1 / ((m : ℝ) + 1) :=
    add_pos (hpos x hx) hepsilon
  have hd := (((ha.contDiffAt (hO.mem_nhds (hpoint x hx))).differentiableAt
    (by simp)).hasFDerivAt.add_const (1 / ((m : ℝ) + 1))).log hden.ne'
  have hnormal : fderiv ℝ (fun q => Real.log (a q + 1 / ((m : ℝ) + 1)))
      (annulusPoint x s) b1 =
        fderiv ℝ a (annulusPoint x s) b1 / (a (annulusPoint x s) + 1 / ((m : ℝ) + 1)) := by
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hnormal]
  dsimp only [F, G]
  field_simp [(hpos x hx).ne']

theorem m64Annulus_log_normal_trace_tendsto
    {a : LoopPlane → ℝ} {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : m64AnnulusDomain ⊆ O) (ha : ContDiffOn ℝ ∞ a O)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (0 : ℝ) curvePeriod, 0 < a (annulusPoint x s)) :
    Tendsto (fun m : ℕ => ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log (a q + 1 / ((m : ℝ) + 1)))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) atTop
      (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ a (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) /
          a (annulusPoint x s))) :=
  m64Annulus_log_normal_trace_tendsto_on_slice hO ha s
    (fun _ hx => hdom ⟨hx.1, hx.2, hs⟩) hpos

end PoincareConjecture

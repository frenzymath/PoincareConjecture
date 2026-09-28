import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CovariantBoundaryFlux
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

private theorem annulusPoint_mem_of_intervals {O : Set LoopPlane}
    (hdom : m64AnnulusDomain ⊆ O) {x s : ℝ}
    (hx : x ∈ Icc (0 : ℝ) curvePeriod) (hs : s ∈ Icc (0 : ℝ) 1) :
    annulusPoint x s ∈ O := by
  apply hdom
  change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
  exact ⟨hx.1, hx.2, hs.1, hs.2⟩




theorem m64Annulus_integral_vertical_derivative_of_contDiffOn
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    {f : LoopPlane → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ p in interior m64AnnulusDomain,
      fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) - f (annulusPoint x 0) := by
  let D := fun p => fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)
  have hD : ContinuousOn D O :=
    ((hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hDi : IntegrableOn D (interior m64AnnulusDomain) volume :=
    (hD.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable D hDi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hcurve : Continuous (fun s : ℝ => annulusPoint x s) := by
    unfold annulusPoint
    fun_prop
  have hd : ContinuousOn (fun s => D (annulusPoint x s)) (Icc (0 : ℝ) 1) :=
    hD.comp hcurve.continuousOn (fun s hs => annulusPoint_mem_of_intervals hdom hx hs)
  have hder (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => f (annulusPoint x r)) (D (annulusPoint x s)) s :=
    ((hf.contDiffAt (hO.mem_nhds (annulusPoint_mem_of_intervals hdom hx hs))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s
      (m64AnnulusPoint_vertical_hasDerivAt x s)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa only [uIcc_of_le zero_le_one] using hs))
    (hd.intervalIntegrable_of_Icc zero_le_one)




theorem m64Annulus_integral_horizontal_derivative_of_contDiffOn
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    {f : LoopPlane → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    (∫ p in interior m64AnnulusDomain,
      fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) =
      ∫ s in Icc (0 : ℝ) 1,
        f (annulusPoint curvePeriod s) - f (annulusPoint 0 s) := by
  let D := fun p => fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)
  have hD : ContinuousOn D O :=
    ((hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hDi : IntegrableOn D (interior m64AnnulusDomain) volume :=
    (hD.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable D hDi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
    unfold annulusPoint
    fun_prop
  have hd : ContinuousOn (fun x => D (annulusPoint x s)) (Icc (0 : ℝ) curvePeriod) :=
    hD.comp hcurve.continuousOn (fun x hx => annulusPoint_mem_of_intervals hdom hx hs)
  have hder (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      HasDerivAt (fun y => f (annulusPoint y s)) (D (annulusPoint x s)) x :=
    ((hf.contDiffAt (hO.mem_nhds (annulusPoint_mem_of_intervals hdom hx hs))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)
  have hp : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hp] using hx))
    (hd.intervalIntegrable_of_Icc hp)

open Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Γ : LoopPlane → LoopPlane →L[ℝ] E →L[ℝ] E}
  {G : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ}
  {V W W0 W1 : LoopPlane → E} {O : Set LoopPlane}

private theorem continuousOn_covariantDerivative
    (hO : IsOpen O) (hΓ : ContinuousOn Γ O) (hV : ContDiffOn ℝ ∞ V O) (d : LoopPlane) :
    ContinuousOn (fun p => covariantDerivative Γ V p d) O := by
  exact (((hV.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn).add
    ((hΓ.clm_apply continuousOn_const).clm_apply hV.continuousOn)

private theorem covariant_pairings_integrable_on
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hΓ : ContinuousOn Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O) (d : LoopPlane) :
    IntegrableOn (fun p => G p (covariantDerivative Γ V p d) (W p))
        (interior m64AnnulusDomain) volume ∧
      IntegrableOn (fun p => G p (V p) (covariantDerivative Γ W p d))
        (interior m64AnnulusDomain) volume := by
  constructor
  · exact (((hG.continuousOn.clm_apply (continuousOn_covariantDerivative hO hΓ hV d)).clm_apply
      hW.continuousOn).mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  · exact (((hG.continuousOn.clm_apply hV.continuousOn).clm_apply
      (continuousOn_covariantDerivative hO hΓ hW d)).mono hdom).integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset

private theorem integral_covariant_pairing_on_eq_integral_derivative
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hΓ : ContinuousOn Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hcompat : ∀ p ∈ O, ∀ d : LoopPlane, ∀ v w : E,
      fderiv ℝ (fun q => G q v w) p d =
        G p (Γ p d v) w + G p v (Γ p d w)) (d : LoopPlane) :
    (∫ p in interior m64AnnulusDomain, G p (covariantDerivative Γ V p d) (W p)) +
      (∫ p in interior m64AnnulusDomain, G p (V p) (covariantDerivative Γ W p d)) =
        ∫ p in interior m64AnnulusDomain, fderiv ℝ (fun q => G q (V q) (W q)) p d := by
  obtain ⟨hleft, hright⟩ := covariant_pairings_integrable_on hO hdom hΓ hG hV hW d
  rw [← integral_add hleft hright]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  have hpo := hdom (interior_subset hp)
  exact (fderiv_metric_pairing
    ((hG.contDiffAt (hO.mem_nhds hpo)).differentiableAt (by simp))
    ((hV.contDiffAt (hO.mem_nhds hpo)).differentiableAt (by simp))
    ((hW.contDiffAt (hO.mem_nhds hpo)).differentiableAt (by simp))
    (hcompat p hpo) d).symm





theorem m64Annulus_covariant_boundary_flux_on
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hΓ : ContinuousOn Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW0 : ContDiffOn ℝ ∞ W0 O) (hW1 : ContDiffOn ℝ ∞ W1 O)
    (hcompat : ∀ p ∈ O, ∀ d : LoopPlane, ∀ v w : E,
      fderiv ℝ (fun q => G q v w) p d =
        G p (Γ p d v) w + G p v (Γ p d w))
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      G (annulusPoint curvePeriod s) (V (annulusPoint curvePeriod s))
        (W0 (annulusPoint curvePeriod s)) =
      G (annulusPoint 0 s) (V (annulusPoint 0 s)) (W0 (annulusPoint 0 s))) :
    (∫ p in interior m64AnnulusDomain,
      G p (covariantDerivative Γ V p (EuclideanSpace.single (0 : Fin 2) 1)) (W0 p) +
        G p (covariantDerivative Γ V p (EuclideanSpace.single (1 : Fin 2) 1)) (W1 p)) +
      (∫ p in interior m64AnnulusDomain, G p (V p)
        (covariantDerivative Γ W0 p (EuclideanSpace.single (0 : Fin 2) 1) +
          covariantDerivative Γ W1 p (EuclideanSpace.single (1 : Fin 2) 1))) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        G (annulusPoint x 1) (V (annulusPoint x 1)) (W1 (annulusPoint x 1)) -
          G (annulusPoint x 0) (V (annulusPoint x 0)) (W1 (annulusPoint x 0)) := by
  have hi0 := covariant_pairings_integrable_on hO hdom hΓ hG hV hW0
    (EuclideanSpace.single (0 : Fin 2) 1)
  have hi1 := covariant_pairings_integrable_on hO hdom hΓ hG hV hW1
    (EuclideanSpace.single (1 : Fin 2) 1)
  have hh := integral_covariant_pairing_on_eq_integral_derivative hO hdom hΓ hG hV hW0
    hcompat (EuclideanSpace.single (0 : Fin 2) 1)
  have hv := integral_covariant_pairing_on_eq_integral_derivative hO hdom hΓ hG hV hW1
    hcompat (EuclideanSpace.single (1 : Fin 2) 1)
  rw [m64Annulus_integral_horizontal_derivative_of_contDiffOn hO hdom
    ((hG.clm_apply hV).clm_apply hW0)] at hh
  rw [m64Annulus_integral_vertical_derivative_of_contDiffOn hO hdom
    ((hG.clm_apply hV).clm_apply hW1)] at hv
  have hzero : (∫ s in Icc (0 : ℝ) 1,
      G (annulusPoint curvePeriod s) (V (annulusPoint curvePeriod s))
          (W0 (annulusPoint curvePeriod s)) -
        G (annulusPoint 0 s) (V (annulusPoint 0 s)) (W0 (annulusPoint 0 s))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact sub_eq_zero.mpr (hseam s hs)
  rw [hzero] at hh
  simp_rw [map_add]
  rw [integral_add hi0.1 hi1.1, integral_add hi0.2 hi1.2]
  linarith

end PoincareConjecture

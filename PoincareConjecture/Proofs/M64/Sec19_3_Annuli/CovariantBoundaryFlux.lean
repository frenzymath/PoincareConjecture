import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity
import PoincareConjecture.Proofs.M60.Mathlib.CovariantPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

open Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Γ : LoopPlane → LoopPlane →L[ℝ] E →L[ℝ] E}
  {G : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ}
  {V W W0 W1 : LoopPlane → E}

private theorem continuous_covariantDerivative
    (hΓ : Continuous Γ) (hV : ContDiff ℝ 1 V) (d : LoopPlane) :
    Continuous (fun p => covariantDerivative Γ V p d) := by
  exact ((hV.continuous_fderiv (by simp)).clm_apply continuous_const).add
    ((hΓ.clm_apply continuous_const).clm_apply hV.continuous)

private theorem covariant_pairings_integrable
    (hΓ : Continuous Γ) (hG : ContDiff ℝ 1 G)
    (hV : ContDiff ℝ 1 V) (hW : ContDiff ℝ 1 W) (d : LoopPlane) :
    IntegrableOn (fun p => G p (covariantDerivative Γ V p d) (W p))
        (interior m64AnnulusDomain) volume ∧
      IntegrableOn (fun p => G p (V p) (covariantDerivative Γ W p d))
        (interior m64AnnulusDomain) volume := by
  constructor
  · exact ((hG.continuous.clm_apply (continuous_covariantDerivative hΓ hV d)).clm_apply
      hW.continuous).continuousOn.integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  · exact ((hG.continuous.clm_apply hV.continuous).clm_apply
      (continuous_covariantDerivative hΓ hW d)).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset

private theorem integral_covariant_pairing_eq_integral_derivative
    (hΓ : Continuous Γ) (hG : ContDiff ℝ 1 G)
    (hV : ContDiff ℝ 1 V) (hW : ContDiff ℝ 1 W)
    (hcompat : ∀ p ∈ interior m64AnnulusDomain, ∀ d : LoopPlane, ∀ v w : E,
      fderiv ℝ (fun q => G q v w) p d =
        G p (Γ p d v) w + G p v (Γ p d w)) (d : LoopPlane) :
    (∫ p in interior m64AnnulusDomain, G p (covariantDerivative Γ V p d) (W p)) +
      (∫ p in interior m64AnnulusDomain, G p (V p) (covariantDerivative Γ W p d)) =
        ∫ p in interior m64AnnulusDomain, fderiv ℝ (fun q => G q (V q) (W q)) p d := by
  obtain ⟨hleft, hright⟩ := covariant_pairings_integrable hΓ hG hV hW d
  rw [← integral_add hleft hright]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  exact (fderiv_metric_pairing (hG.differentiable (by simp) p)
    (hV.differentiable (by simp) p) (hW.differentiable (by simp) p)
    (hcompat p hp) d).symm

theorem m64Annulus_covariant_vertical_green_identity
    (hΓ : Continuous Γ) (hG : ContDiff ℝ 1 G)
    (hV : ContDiff ℝ 1 V) (hW : ContDiff ℝ 1 W)
    (hcompat : ∀ p ∈ interior m64AnnulusDomain, ∀ d : LoopPlane, ∀ v w : E,
      fderiv ℝ (fun q => G q v w) p d =
        G p (Γ p d v) w + G p v (Γ p d w)) :
    (∫ p in interior m64AnnulusDomain,
      G p (covariantDerivative Γ V p (EuclideanSpace.single (1 : Fin 2) 1)) (W p)) +
      (∫ p in interior m64AnnulusDomain,
        G p (V p) (covariantDerivative Γ W p (EuclideanSpace.single (1 : Fin 2) 1))) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        G (annulusPoint x 1) (V (annulusPoint x 1)) (W (annulusPoint x 1)) -
          G (annulusPoint x 0) (V (annulusPoint x 0)) (W (annulusPoint x 0)) := by
  rw [integral_covariant_pairing_eq_integral_derivative hΓ hG hV hW hcompat]
  exact m64Annulus_integral_vertical_derivative ((hG.clm_apply hV).clm_apply hW)

theorem m64Annulus_covariant_horizontal_green_identity
    (hΓ : Continuous Γ) (hG : ContDiff ℝ 1 G)
    (hV : ContDiff ℝ 1 V) (hW : ContDiff ℝ 1 W)
    (hcompat : ∀ p ∈ interior m64AnnulusDomain, ∀ d : LoopPlane, ∀ v w : E,
      fderiv ℝ (fun q => G q v w) p d =
        G p (Γ p d v) w + G p v (Γ p d w)) :
    (∫ p in interior m64AnnulusDomain,
      G p (covariantDerivative Γ V p (EuclideanSpace.single (0 : Fin 2) 1)) (W p)) +
      (∫ p in interior m64AnnulusDomain,
        G p (V p) (covariantDerivative Γ W p (EuclideanSpace.single (0 : Fin 2) 1))) =
      ∫ s in Icc (0 : ℝ) 1,
        G (annulusPoint curvePeriod s) (V (annulusPoint curvePeriod s))
          (W (annulusPoint curvePeriod s)) -
          G (annulusPoint 0 s) (V (annulusPoint 0 s)) (W (annulusPoint 0 s)) := by
  rw [integral_covariant_pairing_eq_integral_derivative hΓ hG hV hW hcompat]
  exact m64Annulus_integral_horizontal_derivative ((hG.clm_apply hV).clm_apply hW)

theorem m64Annulus_covariant_boundary_flux
    (hΓ : Continuous Γ) (hG : ContDiff ℝ 1 G)
    (hV : ContDiff ℝ 1 V) (hW0 : ContDiff ℝ 1 W0) (hW1 : ContDiff ℝ 1 W1)
    (hcompat : ∀ p ∈ interior m64AnnulusDomain, ∀ d : LoopPlane, ∀ v w : E,
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
  have hi0 := covariant_pairings_integrable hΓ hG hV hW0
    (EuclideanSpace.single (0 : Fin 2) 1)
  have hi1 := covariant_pairings_integrable hΓ hG hV hW1
    (EuclideanSpace.single (1 : Fin 2) 1)
  have hh := m64Annulus_covariant_horizontal_green_identity hΓ hG hV hW0 hcompat
  have hv := m64Annulus_covariant_vertical_green_identity hΓ hG hV hW1 hcompat
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

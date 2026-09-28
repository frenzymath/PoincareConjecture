import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapMinimalBoundary
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : LoopPlane → LoopPlane →L[ℝ] E →L[ℝ] E}
  {G : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ}
  {V W W0 W1 : LoopPlane → E} {O : Set LoopPlane}

private theorem supported_metric_pairing_contDiff
    (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hVO : tsupport V ⊆ O) : ContDiff ℝ ∞ (fun p => G p (V p) (W p)) := by
  apply M60.contDiff_of_support_subset_closed (isClosed_tsupport V) hO hVO
    ((hG.clm_apply hV).clm_apply hW)
  intro p hp
  apply subset_tsupport
  intro hz
  exact hp (by simp only [hz, map_zero, zero_apply])

private theorem supported_metric_pairing_fderiv
    (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hVO : tsupport V ⊆ O)
    (hcompat : ∀ p ∈ O, ∀ d : LoopPlane, ∀ a b : E,
      fderiv ℝ (fun q => G q a b) p d = G p (C p d a) b + G p a (C p d b))
    (p d : LoopPlane) :
    fderiv ℝ (fun q => G q (V q) (W q)) p d =
      G p (covariantDerivative C V p d) (W p) +
        G p (V p) (covariantDerivative C W p d) := by
  by_cases hp : p ∈ tsupport V
  · exact fderiv_metric_pairing
      ((hG.contDiffAt (hO.mem_nhds (hVO hp))).differentiableAt (by simp))
      ((hV.contDiffAt (hO.mem_nhds (hVO hp))).differentiableAt (by simp))
      ((hW.contDiffAt (hO.mem_nhds (hVO hp))).differentiableAt (by simp))
      (hcompat p (hVO hp)) d
  · have hzero : (fun q => G q (V q) (W q)) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hp] with q hq
      simp only [image_eq_zero_of_notMem_tsupport hq, map_zero, zero_apply]
    rw [hzero.fderiv_eq]
    simp only [fderiv_const_apply, zero_apply, covariantDerivative,
      image_eq_zero_of_notMem_tsupport hp, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp,
      map_zero, add_zero]

private theorem supported_pairing_integral_eq_derivative
    (hO : IsOpen O) (hC : ContDiffOn ℝ ∞ C O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    (hcompat : ∀ p ∈ O, ∀ d : LoopPlane, ∀ a b : E,
      fderiv ℝ (fun q => G q a b) p d = G p (C p d a) b + G p a (C p d b))
    (d : LoopPlane) :
    (∫ p in interior m64AnnulusDomain, G p (covariantDerivative C V p d) (W p)) +
      (∫ p in interior m64AnnulusDomain, G p (V p) (covariantDerivative C W p d)) =
        ∫ p in interior m64AnnulusDomain, fderiv ℝ (fun q => G q (V q) (W q)) p d := by
  obtain ⟨hleft, hright⟩ := M60.integrable_covariant_pairings (μ := volume)
    hO hC hG hV hW hVc hVO d
  rw [← integral_add hleft.integrableOn hright.integrableOn]
  apply integral_congr_ae
  exact Eventually.of_forall fun p =>
    (supported_metric_pairing_fderiv hO hG hV hW hVO hcompat p d).symm





theorem m64Annulus_covariant_boundary_flux_supported
    (hO : IsOpen O) (hC : ContDiffOn ℝ ∞ C O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW0 : ContDiffOn ℝ ∞ W0 O)
    (hW1 : ContDiffOn ℝ ∞ W1 O) (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    (hcompat : ∀ p ∈ O, ∀ d : LoopPlane, ∀ a b : E,
      fderiv ℝ (fun q => G q a b) p d = G p (C p d a) b + G p a (C p d b))
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      G (annulusPoint curvePeriod s) (V (annulusPoint curvePeriod s))
        (W0 (annulusPoint curvePeriod s)) =
      G (annulusPoint 0 s) (V (annulusPoint 0 s)) (W0 (annulusPoint 0 s))) :
    (∫ p in interior m64AnnulusDomain,
      G p (covariantDerivative C V p (EuclideanSpace.single (0 : Fin 2) 1)) (W0 p) +
        G p (covariantDerivative C V p (EuclideanSpace.single (1 : Fin 2) 1)) (W1 p)) +
      (∫ p in interior m64AnnulusDomain, G p (V p)
        (covariantDerivative C W0 p (EuclideanSpace.single (0 : Fin 2) 1) +
          covariantDerivative C W1 p (EuclideanSpace.single (1 : Fin 2) 1))) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        G (annulusPoint x 1) (V (annulusPoint x 1)) (W1 (annulusPoint x 1)) -
          G (annulusPoint x 0) (V (annulusPoint x 0)) (W1 (annulusPoint x 0)) := by
  have hi0 := M60.integrable_covariant_pairings (μ := volume) hO hC hG hV hW0 hVc hVO
    (EuclideanSpace.single (0 : Fin 2) 1)
  have hi1 := M60.integrable_covariant_pairings (μ := volume) hO hC hG hV hW1 hVc hVO
    (EuclideanSpace.single (1 : Fin 2) 1)
  have hh := supported_pairing_integral_eq_derivative hO hC hG hV hW0 hVc hVO hcompat
    (EuclideanSpace.single (0 : Fin 2) 1)
  have hv := supported_pairing_integral_eq_derivative hO hC hG hV hW1 hVc hVO hcompat
    (EuclideanSpace.single (1 : Fin 2) 1)
  rw [m64Annulus_integral_horizontal_derivative
    ((supported_metric_pairing_contDiff hO hG hV hW0 hVO).of_le (by simp))] at hh
  rw [m64Annulus_integral_vertical_derivative
    ((supported_metric_pairing_contDiff hO hG hV hW1 hVO).of_le (by simp))] at hv
  have hzero : (∫ s in Icc (0 : ℝ) 1,
      G (annulusPoint curvePeriod s) (V (annulusPoint curvePeriod s))
          (W0 (annulusPoint curvePeriod s)) -
        G (annulusPoint 0 s) (V (annulusPoint 0 s)) (W0 (annulusPoint 0 s))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact sub_eq_zero.mpr (hseam s hs)
  rw [hzero] at hh
  simp_rw [map_add]
  rw [integral_add hi0.1.integrableOn hi1.1.integrableOn,
    integral_add hi0.2.integrableOn hi1.2.integrableOn]
  linarith

end PoincareConjecture

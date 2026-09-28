import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakFluxPrimitive
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

def m64HorizontalMoment (theta : ℝ → ℝ) (u : LoopPlane → ℝ) (s : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) curvePeriod, theta x * u (annulusPoint x s)

theorem m64Annulus_continuous_mul_integrable
    {f c : LoopPlane → ℝ} (hf : Integrable f mu) (hc : Continuous c) :
    Integrable (fun p => c p * f p) mu := by
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn hc.continuousOn
  exact hf.bdd_mul hc.aestronglyMeasurable (show ∀ᵐ p ∂mu, ‖c p‖ ≤ C from by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp))

theorem m64HorizontalMoment_integrable
    {theta : ℝ → ℝ} {u : LoopPlane → ℝ} (htheta : Continuous theta)
    (hu : Integrable u mu) :
    IntegrableOn (m64HorizontalMoment theta u) (Icc (0 : ℝ) 1) volume := by
  have hc : Continuous (fun p : LoopPlane => theta (p 0)) :=
    htheta.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous
  have hi := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable
    (m64Annulus_continuous_mul_integrable hu hc)
  exact hi.integral_prod_right

theorem m64HorizontalMoment_pairing
    {theta rho : ℝ → ℝ} {u : LoopPlane → ℝ}
    (htheta : Continuous theta) (hrho : Continuous rho) (hu : Integrable u mu) :
    (∫ s in Icc (0 : ℝ) 1, rho s * m64HorizontalMoment theta u s) =
      ∫ p in S, theta (p 0) * rho (p 1) * u p := by
  have hc : Continuous (fun p : LoopPlane => theta (p 0) * rho (p 1)) :=
    (htheta.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous).mul
      (hrho.comp (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous)
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _
    (m64Annulus_continuous_mul_integrable hu hc)]
  apply integral_congr_ae
  filter_upwards [] with s
  change rho s * (∫ x in Icc (0 : ℝ) curvePeriod, theta x * u (annulusPoint x s)) =
    ∫ x in Icc (0 : ℝ) curvePeriod, theta x * rho s * u (annulusPoint x s)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem m64LocalizedStress_zero_boundary_moment
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hst : ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → HasCompactSupport rho →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0) :
    ContinuousOn
      (fun s => ∫ y in (0 : ℝ)..s, m64HorizontalMoment (deriv eta) U y) (Icc (0 : ℝ) 1) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        m64HorizontalMoment eta V s =
          ∫ y in (0 : ℝ)..s, m64HorizontalMoment (deriv eta) U y) ∧
      (∫ y in (0 : ℝ)..1, m64HorizontalMoment (deriv eta) U y) = 0 := by
  apply m64WeakGreen_zero_boundary_primitive
    (m64HorizontalMoment_integrable heta.continuous hV)
    (m64HorizontalMoment_integrable (heta.continuous_deriv (by simp)) hU)
  intro rho hrho hcompact
  rw [m64HorizontalMoment_pairing heta.continuous (hrho.continuous_deriv (by simp)) hV,
    m64HorizontalMoment_pairing (heta.continuous_deriv (by simp)) hrho.continuous hU,
    add_comm]
  have hcU : Continuous (fun p : LoopPlane => deriv eta (p 0) * rho (p 1)) :=
    ((heta.continuous_deriv (by simp)).comp
      (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous).mul
      (hrho.continuous.comp (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous)
  have hcV : Continuous (fun p : LoopPlane => eta (p 0) * deriv rho (p 1)) :=
    (heta.continuous.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous).mul
      ((hrho.continuous_deriv (by simp)).comp
        (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous)
  rw [← integral_add (m64Annulus_continuous_mul_integrable hU hcU)
    (m64Annulus_continuous_mul_integrable hV hcV)]
  exact hst rho hrho hcompact

end PoincareConjecture

import PoincareConjecture.Proofs.M64.Mathlib.EndpointCutoffIntegral
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressMoments
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open Poincare.Analysis.Sobolev.WeakCompactness

namespace PoincareConjecture

local notation "K" => m64AnnulusDomain
local notation "S" => interior K
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private theorem separable_deriv {eta rho : ℝ → ℝ}
    (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho) (p : LoopPlane) :
    fderiv ℝ (fun q : LoopPlane => eta (q 0) * rho (q 1)) p e0 =
      deriv eta (p 0) * rho (p 1) ∧
    fderiv ℝ (fun q : LoopPlane => eta (q 0) * rho (q 1)) p e1 =
      eta (p 0) * deriv rho (p 1) := by
  have h0 := ((heta.differentiable (by simp) (p 0)).hasDerivAt
    ).comp_hasFDerivAt p ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt)
  have h1 := ((hrho.differentiable (by simp) (p 1)).hasDerivAt
    ).comp_hasFDerivAt p ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt)
  have hd := (h0.mul h1).fderiv
  change fderiv ℝ (fun q : LoopPlane => eta (q 0) * rho (q 1)) p = _ at hd
  rw [hd]
  simp [mul_comm]

private theorem separable_support {eta rho : ℝ → ℝ}
    (heta : tsupport eta ⊆ Ioo (0 : ℝ) curvePeriod)
    (hrho : tsupport rho ⊆ Ioo (0 : ℝ) 1) :
    HasCompactSupport (fun p : LoopPlane => eta (p 0) * rho (p 1)) ∧
      tsupport (fun p : LoopPlane => eta (p 0) * rho (p 1)) ⊆ S := by
  have hsub : tsupport (fun p : LoopPlane => eta (p 0) * rho (p 1)) ⊆ S := by
    intro p hp
    have h0 := heta (tsupport_comp_subset_preimage eta
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous
      (tsupport_mul_subset_left hp))
    have h1 := hrho (tsupport_comp_subset_preimage rho
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
      (tsupport_mul_subset_right hp))
    exact (m64AnnulusInterior_coordinates p).mpr ⟨h0.1, h0.2, h1⟩
  exact ⟨m64AnnulusDomain_isCompact.of_isClosed_subset (isClosed_tsupport _)
    (hsub.trans interior_subset), hsub⟩

theorem m64Annulus_second_stress_compact
    {U V : LoopPlane → ℝ} {c : ℝ}
    (hU : ContDiffOn ℝ 1 U S) (hV : ContDiffOn ℝ 1 V S)
    (hUV : ∀ p ∈ S, fderiv ℝ U p e1 = c * fderiv ℝ V p e0)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho)
    (hetaS : tsupport eta ⊆ Ioo (0 : ℝ) curvePeriod)
    (hrhoS : tsupport rho ⊆ Ioo (0 : ℝ) 1) :
    (∫ p in S, eta (p 0) * deriv rho (p 1) * U p) =
      c * ∫ p in S, deriv eta (p 0) * rho (p 1) * V p := by
  let phi := fun p : LoopPlane => eta (p 0) * rho (p 1)
  have hp : ContDiff ℝ ∞ phi :=
    (heta.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
      (hrho.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
  obtain ⟨hc, hs⟩ := separable_support hetaS hrhoS
  have hu := setIntegral_test_fderiv isOpen_interior hU hp hc hs e1
  have hv := setIntegral_test_fderiv isOpen_interior hV hp hc hs e0
  have heq : (∫ p in S, phi p * fderiv ℝ U p e1) =
      c * ∫ p in S, phi p * fderiv ℝ V p e0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hpS
    rw [hUV p hpS]
    ring
  simp only [smul_eq_mul] at hu hv
  rw [hu, hv] at heq
  have hu' : (∫ p in S, fderiv ℝ phi p e1 * U p) =
      ∫ p in S, eta (p 0) * deriv rho (p 1) * U p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp only [phi]
      rw [(separable_deriv heta hrho p).2]
  have hv' : (∫ p in S, fderiv ℝ phi p e0 * V p) =
      ∫ p in S, deriv eta (p 0) * rho (p 1) * V p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp only [phi]
      rw [(separable_deriv heta hrho p).1]
  rw [hu', hv'] at heq
  linarith

theorem m64Annulus_second_stress_zero_cut
    {U V : LoopPlane → ℝ} {c : ℝ}
    (hU : ContDiffOn ℝ 1 U S) (hV : ContDiffOn ℝ 1 V S)
    (hUi : Integrable U mu) (hVi : Integrable V mu)
    (hUV : ∀ p ∈ S, fderiv ℝ U p e1 = c * fderiv ℝ V p e0)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho)
    (heta0 : eta 0 = 0) (hetaP : eta curvePeriod = 0)
    (hrhoS : tsupport rho ⊆ Ioo (0 : ℝ) 1) :
    (∫ p in S, eta (p 0) * deriv rho (p 1) * U p) =
      c * ∫ p in S, deriv eta (p 0) * rho (p 1) * V p := by
  have hI : ∀ᵐ p ∂mu, p 0 ∈ Ioo (0 : ℝ) curvePeriod := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    have hh := (m64AnnulusInterior_coordinates p).mp hp
    exact ⟨hh.1, hh.2.1⟩
  have hleft := (m64EndpointCutoff_integral_tendsto
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable hI
    (m64Annulus_continuous_mul_integrable hUi
      ((hrho.continuous_deriv (by simp)).comp (EuclideanSpace.proj 1).continuous))
    heta heta0 hetaP).1
  have hright := (m64EndpointCutoff_integral_tendsto
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable hI
    (m64Annulus_continuous_mul_integrable hVi
      (hrho.continuous.comp (EuclideanSpace.proj 1).continuous))
    heta heta0 hetaP).2.const_mul c
  simp only [smul_eq_mul, ← mul_assoc] at hleft hright
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [] with j
  exact (m64Annulus_second_stress_compact hU hV hUV
    (m64EndpointCutoff_contDiff heta j) hrho
    (m64EndpointCutoff_compact j).2 hrhoS).symm

end PoincareConjecture

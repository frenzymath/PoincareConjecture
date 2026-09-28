import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamSobolevTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64WeakPartial_ae_zero_off_closed
    {K : Set LoopPlane} (hK : IsClosed K) {u W : LoopPlane → ℝ} {i : Fin 2}
    (hW : MemLp W 2 volume) (hw : HasWeakPartialDeriv i W u univ)
    (hu : ∀ p, p ∉ K → u p = 0) : ∀ᵐ p ∂volume, p ∉ K → W p = 0 := by
  have hueq : u =ᵐ[volume.restrict Kᶜ] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem hK.measurableSet.compl] with p hp
    exact hu p hp
  have hz : HasWeakPartialDeriv i (fun _ : LoopPlane => (0 : ℝ)) (fun _ => 0) Kᶜ := by
    intro phi hp hc hs
    simp
  have hlocal := m64WeakPartialDeriv_ae_congr hueq EventuallyEq.rfl
    (hw.restrict hK.isOpen_compl (subset_univ _))
  have heq := hlocal.ae_eq hK.isOpen_compl hz
    ((hW.restrict Kᶜ).locallyIntegrable (by norm_num))
    (locallyIntegrable_zero (μ := volume.restrict Kᶜ))
  exact (ae_restrict_iff' hK.measurableSet.compl).mp heq

theorem m64WeakPhase_compact_green
    {K S : Set LoopPlane} (hK : IsCompact K) (hKS : K ⊆ S)
    {u W : LoopPlane → ℝ} {i : Fin 2}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : HasWeakPartialDeriv i W u univ) (hsupport : ∀ p, p ∉ K → u p = 0)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * W p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) = 0 := by
  obtain ⟨chi, hchi, hc, hrange, hone, -⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      hK isOpen_univ (subset_univ _)
  let psi := fun p => chi p * phi p
  have hp : ContDiff ℝ 1 psi := (hchi.of_le (by simp)).mul hphi
  have hpc : HasCompactSupport psi := hc.mul_right
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hpc hp (by norm_num)
  have hchiD (p : LoopPlane) (hpK : p ∈ K) : fderiv ℝ chi p = 0 := by
    have hmax : IsLocalMax chi p := Eventually.of_forall fun q => by
      rw [hone p hpK]
      exact (hrange (mem_range_self q)).2
    exact hmax.fderiv_eq_zero
  have hD (p : LoopPlane) (hpK : p ∈ K) :
      fderiv ℝ psi p = fderiv ℝ phi p := by
    dsimp only [psi]
    rw [fderiv_fun_mul (hchi.differentiable (by simp) p) (hphi.differentiable (by simp) p),
      hone p hpK, hchiD p hpK]
    simp
  have hzero := m64WeakPartial_ae_zero_off_closed hK.isClosed hW hw hsupport
  have hleft : (∫ p, u p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
      ∫ p, u p * fderiv ℝ phi p (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hpK : p ∈ K
    · rw [hD p hpK]
    · rw [hsupport p hpK, zero_mul, zero_mul]
  have hright : (∫ p, W p * psi p) = ∫ p, W p * phi p := by
    apply integral_congr_ae
    filter_upwards [hzero] with p hp
    by_cases hpK : p ∈ K
    · simp only [psi, hone p hpK, one_mul]
    · rw [hp hpK, zero_mul, zero_mul]
  have hflux := m64WeakPartial_compact_lipschitz_test hu hW hw hLip hpc
  rw [hleft, hright] at hflux
  have hWI : (∫ p in S, phi p * W p) = ∫ p, phi p * W p := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with p hp hpS
    rw [hp (fun hpK => hpS (hKS hpK)), mul_zero]
  have huI : (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      ∫ p, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hpS
    rw [hsupport p (fun hpK => hpS (hKS hpK)), mul_zero]
  rw [hWI, huI]
  calc
    _ = (∫ p, W p * phi p) +
        (∫ p, u p * fderiv ℝ phi p (EuclideanSpace.single i 1)) := by
      congr 1
      · exact integral_congr_ae (Eventually.of_forall fun p => mul_comm (phi p) (W p))
      · exact integral_congr_ae (Eventually.of_forall fun p =>
          mul_comm (fderiv ℝ phi p (EuclideanSpace.single i 1)) (u p))
    _ = 0 := by rw [hflux]; ring

end PoincareConjecture

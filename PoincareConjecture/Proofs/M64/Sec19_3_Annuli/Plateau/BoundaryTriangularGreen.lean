import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularCofactor
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularMeasure
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



theorem m64TriangularSource_horizontal_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) (u V : LoopPlane → E)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • ((fderiv ℝ T p e0 0) • V (T p))) +
      (∫ p in S, fderiv ℝ phi p e0 • u (T p)) =
    (∫ p in S, (phi ∘ T.symm) p • V p) +
      (∫ p in S, fderiv ℝ (phi ∘ T.symm) p e0 • u p) := by
  let psi := phi ∘ T.symm
  have hpsi : ContDiff ℝ 1 psi := hp.comp (hi.of_le (by simp))
  have heq : psi ∘ T = phi := by funext p; simp [psi]
  have hd (p : LoopPlane) : fderiv ℝ T p e0 0 * fderiv ℝ psi (T p) e0 =
      fderiv ℝ phi p e0 := by
    have h := m64TriangularSource_scalar_comp_zero (hT.differentiable (by simp))
      hsecond (hpsi.differentiable (by simp)) p
    rw [heq] at h
    exact h.symm
  change _ = (∫ p in S, psi p • V p) + ∫ p in S, fderiv ℝ psi p e0 • u p
  congr 1
  · calc
      _ = ∫ p in S, fderiv ℝ T p e0 0 • (psi (T p) • V (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp only [psi, Function.comp_apply, Homeomorph.symm_apply_apply]
        exact smul_comm _ _ _
      _ = _ := m64TriangularSource_integral T (hT.differentiable (by simp))
        hsecond hpos hpre (fun p => psi p • V p)
  · calc
      _ = ∫ p in S, fderiv ℝ T p e0 0 • (fderiv ℝ psi (T p) e0 • u (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [← hd, mul_smul]
      _ = _ := m64TriangularSource_integral T (hT.differentiable (by simp))
        hsecond hpos hpre (fun p => fderiv ℝ psi p e0 • u p)



theorem m64TriangularCofactorTest_at_source
    (T : LoopPlane ≃ₜ LoopPlane) (hT : Differentiable ℝ T)
    (hi : Differentiable ℝ T.symm) (hsecond : ∀ p, T p 1 = p 1)
    (phi : LoopPlane → ℝ) (p : LoopPlane) :
    fderiv ℝ T p e0 0 * m64TriangularCofactorTest0 T phi (T p) =
      fderiv ℝ T p e1 0 * phi p ∧
    fderiv ℝ T p e0 0 * m64TriangularCofactorTest1 T phi (T p) = phi p := by
  have hinv := m64TriangularSource_inverse_derivative T hT hi hsecond p
  simp only [m64TriangularCofactorTest0, m64TriangularCofactorTest1,
    m64Source_first_coordinate_derivative hi, Homeomorph.symm_apply_apply]
  constructor
  · linear_combination -(fderiv ℝ T p e0 0 * phi p) * hinv.2 +
      (fderiv ℝ T p e1 0 * phi p) * hinv.1
  · rw [← mul_assoc, mul_comm (fderiv ℝ T p e0 0), hinv.1, one_mul]




theorem m64TriangularSource_radial_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) {u V0 V1 : LoopPlane → E}
    (hu : MemLp u 2 mu) (hV0 : MemLp V0 2 mu) (hV1 : MemLp V1 2 mu)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • ((fderiv ℝ T p e1 0) • V0 (T p) + V1 (T p))) +
      (∫ p in S, fderiv ℝ phi p e1 • u (T p)) =
    ((∫ p in S, m64TriangularCofactorTest0 T phi p • V0 p) +
      (∫ p in S, fderiv ℝ (m64TriangularCofactorTest0 T phi) p e0 • u p)) +
    ((∫ p in S, m64TriangularCofactorTest1 T phi p • V1 p) +
      (∫ p in S, fderiv ℝ (m64TriangularCofactorTest1 T phi) p e1 • u p)) := by
  let psi0 := m64TriangularCofactorTest0 T phi
  let psi1 := m64TriangularCofactorTest1 T phi
  have ht := hT.differentiable (by simp)
  have hit := hi.differentiable (by simp)
  have hs := m64TriangularCofactorTest_contDiff T hi hp (by simp)
  have hI0 := m64L2_test_integrable hV0 (m64Annulus_continuous_memLp_two hs.1.continuous)
  have hI1 := m64L2_test_integrable hV1 (m64Annulus_continuous_memLp_two hs.2.continuous)
  have hdI0 := m64L2_test_integrable hu (m64Annulus_continuous_memLp_two
    ((hs.1.continuous_fderiv (by simp)).clm_apply (continuous_const (y := e0))))
  have hdI1 := m64L2_test_integrable hu (m64Annulus_continuous_memLp_two
    ((hs.2.continuous_fderiv (by simp)).clm_apply (continuous_const (y := e1))))
  have hvalues : (∫ p in S,
      phi p • ((fderiv ℝ T p e1 0) • V0 (T p) + V1 (T p))) =
      (∫ p in S, psi0 p • V0 p) + ∫ p in S, psi1 p • V1 p := by
    rw [← integral_add hI0 hI1]
    rw [← m64TriangularSource_integral T ht hsecond hpos hpre
      (fun p => psi0 p • V0 p + psi1 p • V1 p)]
    apply integral_congr_ae
    filter_upwards [] with p
    have hv := m64TriangularCofactorTest_at_source T ht hit hsecond phi p
    simp only [smul_add, smul_smul]
    rw [hv.1, hv.2]
    exact congrArg (fun v : E => v + phi p • V1 (T p))
      (by rw [mul_comm])
  have hderivatives : (∫ p in S, fderiv ℝ phi p e1 • u (T p)) =
      (∫ p in S, fderiv ℝ psi0 p e0 • u p) +
        ∫ p in S, fderiv ℝ psi1 p e1 • u p := by
    rw [← integral_add hdI0 hdI1]
    rw [← m64TriangularSource_integral T ht hsecond hpos hpre
      (fun p => fderiv ℝ psi0 p e0 • u p + fderiv ℝ psi1 p e1 • u p)]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [← add_smul, ← mul_smul, m64TriangularCofactor_divergence T hi hsecond hp,
      Homeomorph.symm_apply_apply, m64Source_first_coordinate_derivative hit,
      ← mul_assoc, mul_comm (fderiv ℝ T p e0 0),
      (m64TriangularSource_inverse_derivative T ht hit hsecond p).1, one_mul]
  rw [hvalues, hderivatives]
  abel

end PoincareConjecture

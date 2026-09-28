import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseSeamGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation



theorem m64AnnulusSeam_shifted_derivative_integral {phi : LoopPlane → ℝ}
    (hp : ContDiff ℝ ∞ phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in S, fderiv ℝ phi (p - v) (EuclideanSpace.single i 1)) =
      if i = 0 then ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint 0 s) else 0 := by
  have hf : ContDiff ℝ 1 (fun p => phi (p - v)) :=
    (hp.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  rcases (show i = 0 ∨ i = 1 from by omega) with rfl | rfl
  · have h := m64Annulus_integral_horizontal_derivative hf
    simp only [fderiv_comp_sub, m64AnnulusPoint_sub_seamTranslation, sub_self] at h
    simp only [ite_true]
    rw [h]
    apply integral_congr_ae
    filter_upwards [] with s
    have hz : phi (annulusPoint (-curvePeriod) s) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (-curvePeriod)) (hs h).1)
    simp only [zero_sub, hz, sub_zero]
  · have h := m64Annulus_integral_vertical_derivative hf
    simp only [fderiv_comp_sub, m64AnnulusPoint_sub_seamTranslation] at h
    simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false]
    rw [h]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    have h0 : phi (annulusPoint (x - curvePeriod) 0) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (hs h).2.2.1)
    have h1 : phi (annulusPoint (x - curvePeriod) 1) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (1 : ℝ)) (hs h).2.2.2)
    rw [h0, h1, sub_self]
    rfl

namespace M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}



theorem phase_seam_folded_green
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in S, (phi p + phi (p - v)) * A.phaseColumn i p) +
      (∫ p in S, (fderiv ℝ phi p (EuclideanSpace.single i 1) +
        fderiv ℝ phi (p - v) (EuclideanSpace.single i 1)) * A.phase p) =
      D * ∫ p in S, fderiv ℝ phi (p - v) (EuclideanSpace.single i 1) := by
  rw [m64AnnulusSeam_shifted_derivative_integral hp hs i]
  have hpsi := (m64AnnulusSeamTest_contDiff hp).of_le (m := 1) (by simp)
  rcases (show i = 0 ∨ i = 1 from by omega) with rfl | rfl
  · simp only [ite_true]
    have h := A.phase_seam (m64AnnulusSeamTest phi) hpsi
      (fun s _ => m64AnnulusSeamTest_periodic_boundary hs s)
    have heq (s : ℝ) : m64AnnulusSeamTest phi (annulusPoint curvePeriod s) =
        phi (annulusPoint 0 s) := by
      have hz : phi (annulusPoint curvePeriod s) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl curvePeriod) (hs h).2.1)
      simp only [m64AnnulusSeamTest, m64AnnulusPoint_sub_seamTranslation, sub_self,
        hz, zero_add]
    simp_rw [heq] at h
    simpa only [m64AnnulusSeamTest_fderiv hp, m64AnnulusSeamTest] using h
  · simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false, mul_zero]
    have h := A.phase_boundary (m64AnnulusSeamTest phi) hpsi
    simp only [(m64AnnulusSeamTest_radial_boundary hs _).1,
      (m64AnnulusSeamTest_radial_boundary hs _).2, zero_mul, sub_zero, integral_zero] at h
    simpa only [m64AnnulusSeamTest_fderiv hp, m64AnnulusSeamTest] using h

end M64FreeWeakPhaseAnnulus
end PoincareConjecture

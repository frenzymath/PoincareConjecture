import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMeasurableVerticalGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem m64Annulus_scalar_weak_of_green
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ} {b0 b1 : ℝ → ℝ} {D : ℝ}
    (hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * b1 x - phi (annulusPoint x 0) * b0 x)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) :
    ∀ i, HasWeakPartialDeriv i (V i) u S := by
  intro i phi hp _hsupport hinside
  have hz {p : LoopPlane} (h : p ∉ S) : phi p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => h (hinside ht))
  have h0 (s : ℝ) : phi (annulusPoint 0 s) = 0 := hz (by
    intro h
    exact lt_irrefl (0 : ℝ) ((m64AnnulusInterior_coordinates _).mp h).1)
  have hP (s : ℝ) : phi (annulusPoint curvePeriod s) = 0 := hz (by
    intro h
    exact lt_irrefl curvePeriod ((m64AnnulusInterior_coordinates _).mp h).2.1)
  have hlo (x : ℝ) : phi (annulusPoint x 0) = 0 := hz (by
    intro h
    exact lt_irrefl (0 : ℝ) ((m64AnnulusInterior_coordinates _).mp h).2.2.1)
  have hhi (x : ℝ) : phi (annulusPoint x 1) = 0 := hz (by
    intro h
    exact lt_irrefl (1 : ℝ) ((m64AnnulusInterior_coordinates _).mp h).2.2.2)
  have heq : (∫ p in S, phi p * V i p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) = 0 := by
    fin_cases i
    · have h := hseam phi (hp.of_le (by simp)) (fun s _ => by rw [hP, h0])
      simp only [hP, integral_zero, mul_zero] at h
      convert! h using 1
    · have h := hboundary phi (hp.of_le (by simp))
      simp only [hlo, hhi, zero_mul, sub_zero, integral_zero] at h
      convert! h using 1
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [mul_comm, add_comm] using heq




theorem m64Annulus_vertical_green_sub_const
    {u V : LoopPlane → ℝ} {b0 b1 : ℝ → ℝ}
    (hu : MemLp u 2 mu) (hb0 : Continuous b0) (hb1 : Continuous b1)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * b1 x - phi (annulusPoint x 0) * b0 x)
    (C : ℝ) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * (u p - C)) =
      ∫ x in I, phi (annulusPoint x 1) * (b1 x - C) -
        phi (annulusPoint x 0) * (b0 x - C) := by
  have hd : MemLp (fun p : LoopPlane => fderiv ℝ phi p e1) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hC : MemLp (fun _ : LoopPlane => C) 2 mu :=
    m64Annulus_continuous_memLp_two continuous_const
  have hslice (s : ℝ) : Continuous (fun x => phi (annulusPoint x s)) := by
    apply hp.continuous.comp
    unfold annulusPoint
    fun_prop
  have hi : IntegrableOn (fun x => phi (annulusPoint x 1) * b1 x -
      phi (annulusPoint x 0) * b0 x) I :=
    (((hslice 1).mul hb1).sub ((hslice 0).mul hb0)).integrableOn_Icc
  have hci : IntegrableOn (fun x => phi (annulusPoint x 1) * C -
      phi (annulusPoint x 0) * C) I :=
    (((hslice 1).mul_const C).sub ((hslice 0).mul_const C)).integrableOn_Icc
  have hdu : Integrable (fun p => fderiv ℝ phi p e1 * u p) mu := hd.integrable_mul hu
  have hdc : Integrable (fun p => fderiv ℝ phi p e1 * C) mu := hd.integrable_mul hC
  simp_rw [mul_sub]
  rw [integral_sub hdu hdc, ← add_sub_assoc,
    hgreen phi hp, m64Annulus_measurable_vertical_green (memLp_const C) hp,
    ← integral_sub hi hci]
  apply integral_congr_ae
  filter_upwards [] with x
  ring




theorem m64Annulus_seam_green_sub_const
    {u V : LoopPlane → ℝ} {D : ℝ} (hu : MemLp u 2 mu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (C : ℝ) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (hs : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e0 * (u p - C)) =
      D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
  have hd : MemLp (fun p : LoopPlane => fderiv ℝ phi p e0) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hC : MemLp (fun _ : LoopPlane => C) 2 mu :=
    m64Annulus_continuous_memLp_two continuous_const
  have hz : (∫ p in S, fderiv ℝ phi p e0 * C) = 0 := by
    rw [integral_mul_const, m64Annulus_integral_horizontal_derivative hp]
    have hzero : (∫ s in Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) - phi (annulusPoint 0 s)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hsmem
      rw [hs s hsmem, sub_self]
      rfl
    rw [hzero, zero_mul]
  have hdu : Integrable (fun p => fderiv ℝ phi p e0 * u p) mu := hd.integrable_mul hu
  have hdc : Integrable (fun p => fderiv ℝ phi p e0 * C) mu := hd.integrable_mul hC
  simp_rw [mul_sub]
  rw [integral_sub hdu hdc, hz, sub_zero]
  exact hgreen phi hp hs

end PoincareConjecture

import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceHorizontalWeak







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



theorem m64HorizontalSource_boundary_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : Differentiable ℝ tau) (hi : Differentiable ℝ tau.symm)
    (hmono : StrictMono tau) (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (phi : LoopPlane → ℝ) (b0 b1 : ℝ → E) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      m64HorizontalSourceRadialTest tau phi (annulusPoint x 1) • b1 x -
        m64HorizontalSourceRadialTest tau phi (annulusPoint x 0) • b0 x) =
    ∫ x in Icc (0 : ℝ) curvePeriod,
      phi (annulusPoint x 1) • b1 (tau x) - phi (annulusPoint x 0) • b0 (tau x) := by
  rw [← m64HorizontalSource_interval_integral ht hmono h0 hP]
  apply integral_congr_ae
  filter_upwards [] with x
  have hpoint (s : ℝ) :
      m64HorizontalSourceRadialTest tau phi (annulusPoint (tau x) s) =
        deriv tau.symm (tau x) * phi (annulusPoint x s) := by
    simp only [m64HorizontalSourceRadialTest, m64HorizontalSource_symm,
      m64HorizontalSource_point, Homeomorph.symm_apply_apply]
    rfl
  have hmul (s : ℝ) : deriv tau x *
      (deriv tau.symm (tau x) * phi (annulusPoint x s)) = phi (annulusPoint x s) := by
    rw [← mul_assoc, m64HorizontalSource_inverse_deriv ht hi, one_mul]
  simp only [smul_sub, hpoint, ← mul_smul, hmul]



theorem m64HorizontalSource_preserves_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (u V : LoopPlane → E) (b0 b1 : ℝ → E)
    (hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p e1 • u p) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) • b1 x - phi (annulusPoint x 0) • b0 x) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • V (m64HorizontalSource tau p)) +
        (∫ p in S, fderiv ℝ phi p e1 • u (m64HorizontalSource tau p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • b1 (tau x) - phi (annulusPoint x 0) • b0 (tau x) := by
  intro phi hp
  rw [m64HorizontalSource_radial_green ht hi hpos hmono h0 hP u V hp,
    hboundary _ (m64HorizontalSourceRadialTest_contDiff hi hp (by simp)),
    m64HorizontalSource_boundary_integral (ht.differentiable (by simp))
      (hi.differentiable (by simp)) hmono h0 hP]



theorem m64HorizontalSource_preserves_seam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (u V : LoopPlane → E) (d : E)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p e0 • u p) =
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • d) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • (deriv tau (p 0) • V (m64HorizontalSource tau p))) +
        (∫ p in S, fderiv ℝ phi p e0 • u (m64HorizontalSource tau p)) =
      (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • d := by
  intro phi hp hs
  have hi0 : tau.symm 0 = 0 := by
    simpa only [h0] using tau.symm_apply_apply 0
  have hiP : tau.symm curvePeriod = curvePeriod := by
    simpa only [hP] using tau.symm_apply_apply curvePeriod
  have hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      (phi ∘ (m64HorizontalSource tau).symm) (annulusPoint curvePeriod s) =
        (phi ∘ (m64HorizontalSource tau).symm) (annulusPoint 0 s) := by
    intro s hsI
    simpa only [Function.comp_apply, m64HorizontalSource_symm,
      m64HorizontalSource_point, hi0, hiP] using hs s hsI
  have htest : ContDiff ℝ 1 (phi ∘ (m64HorizontalSource tau).symm) :=
    hp.comp (m64HorizontalSource_contDiff (hi.of_le (by simp)))
  rw [m64HorizontalSource_horizontal_green ht hi hpos hmono h0 hP u V hp,
    hseam _ htest hperiod]
  simp only [Function.comp_apply, m64HorizontalSource_symm, m64HorizontalSource_point, hiP]

end PoincareConjecture

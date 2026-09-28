import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFluxTraceBound
import Mathlib.Analysis.Calculus.FDeriv.Symmetric












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem m64WeakPhase_rotated_test_identity
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) = 0)
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    (eta : LoopPlane → ℝ) (heta : ContDiff ℝ ∞ eta)
    (hleft : ∀ s : ℝ, fderiv ℝ eta (annulusPoint 0 s) e1 = 0)
    (hright : ∀ s : ℝ, fderiv ℝ eta (annulusPoint curvePeriod s) e1 = 0)
    (htop : ∀ x : ℝ, fderiv ℝ eta (annulusPoint x 1) e0 = 0) :
    (∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ eta (annulusPoint x 0) e0 * b x) =
      (∫ p in S, fderiv ℝ eta p e1 * V 0 p) -
        ∫ p in S, fderiv ℝ eta p e0 * V 1 p := by
  let d : Fin 2 → LoopPlane → ℝ := fun i p =>
    fderiv ℝ eta p (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : ContDiff ℝ 1 (d i) :=
    (heta.fderiv_right (m := 1) (by norm_cast : (1 : ℕ∞ω) + 1 ≤ ∞)).clm_apply
      contDiff_const
  have hfd (p : LoopPlane) : DifferentiableAt ℝ (fderiv ℝ eta) p :=
    ((heta.contDiffAt).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hswap (p : LoopPlane) : fderiv ℝ (d 1) p e0 = fderiv ℝ (d 0) p e1 := by
    have hsymm := (heta.contDiffAt (x := p)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) e0 e1
    change fderiv ℝ (fderiv ℝ eta) p e0 e1 =
      fderiv ℝ (fderiv ℝ eta) p e1 e0 at hsymm
    dsimp only [d]
    rw [fderiv_clm_apply (hfd p) (differentiableAt_const e1),
      fderiv_clm_apply (hfd p) (differentiableAt_const e0)]
    simpa using hsymm
  have h0 := hgreen0 (d 1) (hd 1) hleft hright
  have h1 := hgreen1 (d 0) (hd 0) htop
  simp only [hswap] at h0
  change (∫ x in Icc (0 : ℝ) curvePeriod, d 0 (annulusPoint x 0) * b x) =
    (∫ p in S, d 1 p * V 0 p) - ∫ p in S, d 0 p * V 1 p
  linarith





theorem m64WeakPhase_rotated_test_sq_le
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu)
    (hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) = 0)
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    (eta : LoopPlane → ℝ) (heta : ContDiff ℝ ∞ eta)
    (hleft : ∀ s : ℝ, fderiv ℝ eta (annulusPoint 0 s) e1 = 0)
    (hright : ∀ s : ℝ, fderiv ℝ eta (annulusPoint curvePeriod s) e1 = 0)
    (htop : ∀ x : ℝ, fderiv ℝ eta (annulusPoint x 1) e0 = 0) :
    (∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ eta (annulusPoint x 0) e0 * b x) ^ 2 ≤
      2 * ((∫ p in S, (fderiv ℝ eta p e0) ^ 2) +
        ∫ p in S, (fderiv ℝ eta p e1) ^ 2) *
        ((∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2) := by
  have hd (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ eta p (EuclideanSpace.single i 1)) 2 mu := by
    have hc : Continuous (fun p => fderiv ℝ eta p (EuclideanSpace.single i 1)) :=
      (heta.continuous_fderiv (by simp)).clm_apply continuous_const
    apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    exact (hc.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  rw [m64WeakPhase_rotated_test_identity u V b hgreen0 hgreen1 eta heta hleft hright htop]
  have h0 := M64Uniformization.scalar_integral_mul_sq_le (hd 1) (hV 0)
  have h1 := M64Uniformization.scalar_integral_mul_sq_le (hd 0) (hV 1)
  have hn (f : LoopPlane → ℝ) : 0 ≤ ∫ p in S, f p ^ 2 :=
    integral_nonneg (fun p => sq_nonneg _)
  nlinarith [sq_nonneg ((∫ p in S, fderiv ℝ eta p e1 * V 0 p) +
    ∫ p in S, fderiv ℝ eta p e0 * V 1 p),
    mul_nonneg (hn (fun p => fderiv ℝ eta p e0)) (hn (V 0)),
    mul_nonneg (hn (fun p => fderiv ℝ eta p e1)) (hn (V 1))]

end PoincareConjecture

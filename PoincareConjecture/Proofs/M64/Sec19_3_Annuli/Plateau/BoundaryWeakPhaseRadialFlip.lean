import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakSeamContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusRadialFlip
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem m64Integral_unitInterval_reflect (f : ℝ → ℝ) :
    (∫ s in Icc (0 : ℝ) 1, f (1 - s)) = ∫ s in Icc (0 : ℝ) 1, f s := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1
  simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] using h





theorem m64WeakPartialDeriv_annulusRadialFlip
    {u v : LoopPlane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i v u S) :
    HasWeakPartialDeriv i
      (fun p => (if i = 0 then (1 : ℝ) else -1) * v (T p)) (u ∘ T) S := by
  intro phi hp hc hs
  have hpc : ContDiff ℝ ∞ (phi ∘ T) := hp.comp m64AnnulusRadialFlip_contDiff
  have hps : tsupport (phi ∘ T) ⊆ S := by
    rw [tsupport_comp_eq_preimage]
    intro p hpS
    have hTp : p ∈ T ⁻¹' S := hs hpS
    rwa [m64AnnulusRadialFlip_preimage_interior] at hTp
  have hA := hw (phi ∘ T) hpc (hc.comp_homeomorph T) hps
  have hz : (∫ p in S, (phi ∘ T) p • v p) +
      (∫ p in S, fderiv ℝ (phi ∘ T) p (EuclideanSpace.single i 1) • u p) = 0 := by
    simp only [smul_eq_mul, mul_comm] at hA ⊢
    linarith
  have ht := m64AnnulusRadialFlip_green u v (hp.of_le (by simp)) i
  rw [hz, smul_zero] at ht
  simp only [smul_eq_mul] at ht
  change (∫ p in S, u (T p) * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
    -(∫ p in S, ((if i = 0 then (1 : ℝ) else -1) * v (T p)) * phi p)
  simp only [mul_comm] at ht ⊢
  linarith





theorem m64WeakPhase_radialFlip_seam (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ)
    (D : ℝ)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 (T p)) + (∫ p in S, fderiv ℝ phi p e0 * u (T p)) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
  intro phi hp hs
  have hpc : ContDiff ℝ 1 (phi ∘ T) :=
    hp.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
  have hs' : ∀ s ∈ Icc (0 : ℝ) 1,
      (phi ∘ T) (annulusPoint curvePeriod s) = (phi ∘ T) (annulusPoint 0 s) := by
    intro s hsI
    simp only [Function.comp_apply, m64AnnulusRadialFlip_point]
    exact hs (1 - s) ⟨by linarith [hsI.2], by linarith [hsI.1]⟩
  have ht := m64AnnulusRadialFlip_green u (V 0) hp 0
  simp only [smul_eq_mul, ite_true, one_mul] at ht
  rw [hseam (phi ∘ T) hpc hs'] at ht
  simpa only [Function.comp_apply, m64AnnulusRadialFlip_point,
    m64Integral_unitInterval_reflect (fun s => phi (annulusPoint curvePeriod s))] using ht





theorem m64WeakPhase_radialFlip_lower (u : LoopPlane → ℝ) (v : LoopPlane → ℝ)
    (b : ℝ → ℝ)
    (hupper : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 0) = 0) →
      (∫ p in S, phi p * v p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 1) * b x) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * (-v (T p))) + (∫ p in S, fderiv ℝ phi p e1 * u (T p)) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x) := by
  intro phi hp ht
  have hpc : ContDiff ℝ 1 (phi ∘ T) :=
    hp.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
  have hb : ∀ x : ℝ, (phi ∘ T) (annulusPoint x 0) = 0 := by
    intro x
    simpa only [Function.comp_apply, m64AnnulusRadialFlip_point, sub_zero] using ht x
  have hh := m64AnnulusRadialFlip_green u v hp 1
  simp only [smul_eq_mul, show (1 : Fin 2) ≠ 0 from by decide, ite_false, neg_mul,
    one_mul] at hh
  rw [hupper (phi ∘ T) hpc hb] at hh
  simpa only [Function.comp_apply, m64AnnulusRadialFlip_point, sub_self] using hh





theorem m64WeakPhase_monotone_affine_upper_trace_continuous
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ) (D : ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu) (hb : Monotone b)
    (hperiod : ∀ x, b (x + curvePeriod) = b x + D)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hupper : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 0) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 1) * b x) :
    Continuous b := by
  let W := fun i p => (if i = 0 then (1 : ℝ) else -1) * V i (T p)
  have hW (i : Fin 2) : MemLp (W i) 2 mu :=
    ((hV i).comp_measurePreserving m64AnnulusRadialFlip_restrict_measurePreserving).const_mul _
  apply m64WeakPhase_monotone_affine_trace_continuous (u ∘ T) W b D hW hb hperiod
  · simpa only [W, ite_true, one_mul, Function.comp_apply] using
      m64WeakPhase_radialFlip_seam u V D hseam
  · simpa only [W, show (1 : Fin 2) ≠ 0 from by decide, ite_false, neg_mul, one_mul,
      Function.comp_apply] using m64WeakPhase_radialFlip_lower u (V 1) b hupper

end PoincareConjecture

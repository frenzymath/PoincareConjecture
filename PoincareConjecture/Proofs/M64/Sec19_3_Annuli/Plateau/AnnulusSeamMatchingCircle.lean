import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamCircleTraces
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamReplacementTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => m64AnnulusSeamDomain

theorem M64ObservedWeakAnnulus.exists_seam_matching_circle_of_outer_agreement
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane)
    {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O)
    (hKS : Metric.closedBall a rho ⊆ S)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) O)
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = m64AnnulusSeamExtend A.map p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      ∀ (psi : LoopPlane → ℝ) (L : ℝ≥0), LipschitzWith L psi → HasCompactSupport psi →
        ∀ i : Fin 2,
          (∫ p in Metric.closedBall a r, psi p • V i p) +
            (∫ p in Metric.closedBall a r,
              fderiv ℝ psi p (EuclideanSpace.single i 1) • e (f p)) =
          (∫ p in Metric.closedBall a r,
            psi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
            (∫ p in Metric.closedBall a r,
              fderiv ℝ psi p (EuclideanSpace.single i 1) •
                e (m64AnnulusSeamExtend A.map p)) := by
  have hAgreen := A.seam_local_circle_green a hrho hKS
  have hFgreen := m64WeakMap_local_circle_green hO a hrho hKO (e ∘ f) V hf hV hw
  obtain ⟨s, hs, hgreenA, hgreenF⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Icc (0 : ℝ) 1) ≠ 0 by simp) (hAgreen.and hFgreen)
  let r := rho * Real.exp (-s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hlow : rho * Real.exp (-1) ≤ r :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hs.2)) hrho.le
  have hhigh : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hsmall : Metric.closedBall a r ⊆ Metric.closedBall a rho :=
    Metric.closedBall_subset_closedBall hhigh
  have hsmallO := hsmall.trans hKO
  have hsmallS := hsmall.trans hKS
  have hgreen (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in Metric.closedBall a r, phi p • V i p) +
        (∫ p in Metric.closedBall a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in Metric.closedBall a r,
        phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
        (∫ p in Metric.closedBall a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (m64AnnulusSeamExtend A.map p)) := by
    refine (hgreenF phi hphi i).trans ((congrArg (fun v : E => r • v) ?_).trans
      (hgreenA phi hphi i).symm)
    apply integral_congr_ae
    filter_upwards with x
    have hdist : dist (a + r • angularPoint (x - Real.pi)) a = r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, norm_angularPoint, mul_one]
    have heq := hmatch (a + r • angularPoint (x - Real.pi))
      (by rw [hdist]; exact hlow) (by rw [hdist]; exact hhigh)
    dsimp only [r] at heq
    simp only [Function.comp_apply, heq]
  refine ⟨r, hr, hlow, hhigh, ?_⟩
  intro psi L hpsi hc i
  exact m64MatchingGreen_compact_lipschitz (isCompact_closedBall a r)
    (e ∘ m64AnnulusSeamExtend A.map) (e ∘ f)
    (m64AnnulusSeamExtend (A.column i : LoopPlane → E)) (V i)
    (A.seam_extension_memLp.1.mono_measure (Measure.restrict_mono hsmallS le_rfl))
    (hf.mono_measure (Measure.restrict_mono hsmallO le_rfl))
    ((A.seam_extension_memLp.2 i).mono_measure (Measure.restrict_mono hsmallS le_rfl))
    ((hV i).mono_measure (Measure.restrict_mono hsmallO le_rfl))
    (fun phi hp => hgreen phi hp i) hpsi hc

end PoincareConjecture

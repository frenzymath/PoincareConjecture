import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedMinimum
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

set_option maxHeartbeats 1000000 in

theorem exists_lower_weighted_comparison_of_outer_agreement
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hbound : ∀ q, ‖Q q‖ ≤ C) (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    {U : Set LoopPlane} (hU : IsOpen U) (hUO : U ⊆ O)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKU : closedBall a rho ⊆ U)
    (F f : LoopPlane → M) (hFae : F =ᵐ[volume.restrict O] A.lowerExtensionMap)
    (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict U))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict U))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) U)
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict U,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hfixed : ∀ p ∈ U, p 1 < 0 → f p = c0 (p 0))
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = F p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      (∫ p in ball a r,
        (modulus * Q (A.lowerExtensionMap p)
            (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p) +
          modulus⁻¹ * Q (A.lowerExtensionMap p)
            (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)) / 2) ≤
        ∫ p in ball a r,
          (modulus * Q (f p) (V 0 p) (V 0 p) + modulus⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2 := by
  have hobs : (e ∘ A.lowerExtensionMap) =ᵐ[volume.restrict U] (e ∘ F) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUO hFae] with p hp
    exact congrArg e hp.symm
  have hFM : MemLp (e ∘ F) 2 (volume.restrict U) :=
    ((A.lower_extension_memLp hc0).1.mono_measure
      (Measure.restrict_mono hUO le_rfl)).ae_eq hobs
  have hAM (i : Fin 2) := ((A.lower_extension_memLp hc0).2 i).mono_measure
    (Measure.restrict_mono hUO le_rfl)
  have hAw (i : Fin 2) (j : Fin m) :
      HasWeakPartialDeriv i (fun p => A.lowerExtensionColumn i p j)
        (fun p => e (F p) j) U := by
    apply m64WeakPartialDeriv_ae_congr
      (hobs.mono fun p hp => congrArg (fun v : E => v j) hp) EventuallyEq.rfl
    exact (A.lower_extension_weak_partial hc0 i j).restrict hU hUO
  have hAgreen := m64WeakMap_local_circle_green hU a hrho hKU
    (e ∘ F) A.lowerExtensionColumn hFM hAM hAw
  have hFgreen := m64WeakMap_local_circle_green hU a hrho hKU
    (e ∘ f) V hf hV hw
  obtain ⟨s, hs, hgreenA, hgreenF⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Icc (0 : ℝ) 1) ≠ 0 by simp) (hAgreen.and hFgreen)
  let r := rho * Real.exp (-s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hlow : rho * Real.exp (-1) ≤ r :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hs.2)) hrho.le
  have hhigh : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hsmallU : closedBall a r ⊆ U := (closedBall_subset_closedBall hhigh).trans hKU
  have hballU : ball a r ⊆ U := ball_subset_closedBall.trans hsmallU
  have hgreen (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in ball a r, phi p • V i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in ball a r, phi p • A.lowerExtensionColumn i p) +
        (∫ p in ball a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.lowerExtensionMap p)) := by
    have hsame : (∫ p in closedBall a r, phi p • V i p) +
        (∫ p in closedBall a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in closedBall a r, phi p • A.lowerExtensionColumn i p) +
        (∫ p in closedBall a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (F p)) := by
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
    have hvalue : (∫ p in closedBall a r,
        fderiv ℝ phi p (EuclideanSpace.single i 1) • e (F p)) =
      ∫ p in closedBall a r,
        fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.lowerExtensionMap p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsmallU.trans hUO) hFae]
        with p hp
      rw [hp]
    rw [hvalue] at hsame
    simpa only [setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume a r)] using hsame
  refine ⟨r, hr, hlow, hhigh, ?_⟩
  exact A.weighted_lower_exact_minimum_of_matching_flux hc0 Q hQ hei hbound modulus hmin
    a r (hballU.trans hUO) f V (hf.mono_measure (Measure.restrict_mono hballU le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono hballU le_rfl))
    (fun i => ae_restrict_of_ae_restrict_of_subset hballU (ht i))
    (fun i j => (hw i j).restrict isOpen_ball hballU)
    (fun p hp hp1 => hfixed p (hballU hp) hp1) hgreen

end PoincareConjecture.M64ObservedWeakAnnulus

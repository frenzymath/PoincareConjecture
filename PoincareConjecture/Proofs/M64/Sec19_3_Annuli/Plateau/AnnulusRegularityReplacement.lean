import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMapCircleGreen













set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem M64ObservedWeakAnnulus.exists_replacement_of_outer_agreement
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane)
    {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O)
    (hKS : Metric.closedBall a rho ⊆ S)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) O)
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict O,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = A.map p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
        B.map = (Metric.closedBall a r).piecewise f A.map ∧
        ∀ i, (B.column i : LoopPlane → E) =ᵐ[volume.restrict S]
          (Metric.closedBall a r).piecewise (V i) (A.column i) := by
  classical
  have hAgreen := m64WeakMap_local_circle_green isOpen_interior a hrho hKS
    (e ∘ A.map) (fun i p => A.column i p) A.observed_memLp
    (fun i => Lp.memLp (A.column i)) A.weak_partial
  have hFgreen := m64WeakMap_local_circle_green hO a hrho hKO
    (e ∘ f) V hf hV hw
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
      (∫ p in Metric.closedBall a r, phi p • A.column i p) +
        (∫ p in Metric.closedBall a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) := by
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
  exact A.replace Metric.isClosed_closedBall.measurableSet hsmallS f V
    (hf.mono_measure (Measure.restrict_mono hsmallO le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono hsmallO le_rfl))
    (fun i => (ht i).filter_mono (ae_mono (Measure.restrict_mono hsmallO le_rfl))) hgreen

end PoincareConjecture

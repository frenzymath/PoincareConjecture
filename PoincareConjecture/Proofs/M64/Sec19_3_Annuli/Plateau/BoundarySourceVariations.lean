import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTargetLabelVariations
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseSourcePullback
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64

theorem smooth_periodic_source_variation
    {theta : ℝ → ℝ} (htheta : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod) (hzero : theta 0 = 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∃ tau : ℝ ≃ₜ ℝ,
        (∀ x, tau x = x + t * theta x) ∧ ContDiff ℝ ∞ tau ∧
        ContDiff ℝ ∞ tau.symm ∧ StrictMono tau ∧
        (∀ x, 0 < deriv tau x) ∧ tau 0 = 0 ∧
        ∀ x, tau (x + curvePeriod) = tau x + curvePeriod := by
  obtain ⟨delta, hd, hvar⟩ := smooth_periodic_target_variation htheta hperiod
  refine ⟨delta, hd, ?_⟩
  intro t ht
  obtain ⟨T, hT, hmono, hsurj, hreg, hpos⟩ := hvar t ht
  let O := StrictMono.orderIsoOfSurjective T.map hmono hsurj
  let tau : ℝ ≃ₜ ℝ := O.toHomeomorph
  have hsmooth : ContDiff ℝ ∞ tau := hreg
  have hinv : ContDiff ℝ ∞ tau.symm := tau.contDiff_symm_deriv
    (fun x => (hpos x).ne') (fun x => (hreg.differentiable (by simp) x).hasDerivAt) hsmooth
  refine ⟨tau, hT, hsmooth, hinv, hmono, hpos, ?_, T.period_shift⟩
  change T.map 0 = 0
  rw [hT, hzero, mul_zero, add_zero]

end PoincareConjecture.M64

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem exists_smooth_horizontal_variation
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {theta : ℝ → ℝ} (htheta : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod) (hzero : theta 0 = 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
        (∀ p, B.annulus.map p =
          A.annulus.map (annulusPoint (p 0 + t * theta (p 0)) (p 1))) ∧
        (∀ i, ∀ᵐ p ∂mu, B.annulus.column i p =
          (if i = 0 then 1 + t * deriv theta (p 0) else 1) •
            A.annulus.column i (annulusPoint (p 0 + t * theta (p 0)) (p 1))) ∧
        (∀ x, B.label0 x = A.label0 (x + t * theta x)) ∧
        (∀ x, B.label1 x = A.label1 (x + t * theta x)) := by
  obtain ⟨delta, hd, hvar⟩ := M64.smooth_periodic_source_variation htheta hperiod hzero
  refine ⟨delta, hd, ?_⟩
  intro t ht
  obtain ⟨tau, htau, hs, hi, hm, hp, h0, hperiod⟩ := hvar t ht
  obtain ⟨B, hmap, hcol, hlabel0, hlabel1, -⟩ :=
    A.exists_horizontalSource hs hi hp hm h0 hperiod
  have hsource (p : LoopPlane) : m64HorizontalSource tau p =
      annulusPoint (p 0 + t * theta (p 0)) (p 1) := by
    change annulusPoint (tau (p 0)) (p 1) = _
    rw [htau]
  have hderiv (x : ℝ) : deriv tau x = 1 + t * deriv theta x := by
    have hfun : (tau : ℝ → ℝ) = fun x => x + t * theta x := funext htau
    rw [hfun]
    exact ((hasDerivAt_id x).add
      ((htheta.differentiable (by simp) x).hasDerivAt.const_mul t)).deriv
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hmap, Function.comp_apply, hsource]
  · intro i
    simpa only [hderiv, hsource] using hcol i
  · intro x
    simp only [hlabel0, Function.comp_apply, htau]
  · intro x
    simp only [hlabel1, Function.comp_apply, htau]

end PoincareConjecture.M64FreeWeakPhaseAnnulus

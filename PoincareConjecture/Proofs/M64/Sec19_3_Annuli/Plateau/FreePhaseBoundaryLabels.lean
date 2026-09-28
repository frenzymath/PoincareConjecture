import PoincareConjecture.Proofs.M64.Mathlib.MonotonePhaseInterpolation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

theorem exists_lower_phase_chord_label
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < curvePeriod) :
    ∃ sigma : ℝ → ℝ, Continuous sigma ∧ Monotone sigma ∧
      (∀ x, sigma (x + curvePeriod) = sigma x + curvePeriod) ∧
      sigma 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ x ∈ Icc a b, H0 (sigma x) =
        AffineMap.lineMap (H0 (A.label0 a)) (H0 (A.label0 b)) ((x - a) / (b - a))) ∧
      EqOn sigma A.label0 (Icc 0 curvePeriod \ Icc a b) := by
  obtain ⟨sigma, hc, hm, hp, hzero, hchord, houtside⟩ :=
    m64Monotone_phase_chord_replacement (by unfold curvePeriod; positivity)
      ha hab hb H0 hH0 A.label0 (A.labels_continuous hH0 hH1).1
      A.label0_monotone A.label0_period
  exact ⟨sigma, hc, hm, hp, hzero.symm ▸ A.label0_normalized, hchord, houtside⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus

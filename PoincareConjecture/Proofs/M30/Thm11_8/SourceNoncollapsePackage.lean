import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardGeneralizedConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.SourceVolumeAtPoint
import PoincareConjecture.Proofs.M30.Universe.OutputFiniteNoncollapse
import PoincareConjecture.Proofs.M30.Generalized.Noncollapse

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

structure GeneralizedBlowupConvergenceWithSourceNoncollapse
    (S : GeneralizedBlowupSequence.{u}) (kappa r₀ : ℝ) (T₀ : ℝ≥0∞) where
  convergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)
  source : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)

def generalizedConvergenceWithSourceNoncollapse_of_slabService
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongSlabControlService S kappa r₀ T₀)
    (L : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) :
    GeneralizedBlowupConvergenceWithSourceNoncollapse S kappa r₀ T₀ := by
  exact {
    convergence := L
    source := fun T hT hTT => H.noncollapsedBounds T hT hTT }

theorem source_noncollapse_eventually_on_subsequence
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (L : GeneralizedBlowupConvergenceWithSourceNoncollapse S kappa r₀ T₀)
    (T : ℝ) (hT : 0 < T) (hTT : ENNReal.ofReal T < T₀)
    (A : ℝ) (hA : 0 < A) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (NoncollapsedControlledBlowupCylinder S
            (L.convergence.subsequence k) A T B eta kappa r₀) := by
  obtain ⟨B, hB, hfamily⟩ := L.source T hT hTT
  refine ⟨B, hB, ?_⟩
  exact L.convergence.subsequence_strictMono.tendsto_atTop.eventually
    (hfamily A hA eta heta)

theorem source_noncollapse_eventually_on_subsequence_mono
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ kappa' r₀' : ℝ}
    {T₀ : ℝ≥0∞}
    (L : GeneralizedBlowupConvergenceWithSourceNoncollapse S kappa r₀ T₀)
    (T : ℝ) (hT : 0 < T) (hTT : ENNReal.ofReal T < T₀)
    (A : ℝ) (hA : 0 < A) (eta : ℝ) (heta : 0 < eta)
    (hkappa : kappa' ≤ kappa) (hr₀ : r₀' ≤ r₀) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (NoncollapsedControlledBlowupCylinder S
            (L.convergence.subsequence k) A T B eta kappa' r₀') := by
  obtain ⟨B, hB, hfamily⟩ := L.source T hT hTT
  refine ⟨B, hB, ?_⟩
  filter_upwards [L.convergence.subsequence_strictMono.tendsto_atTop.eventually
    (hfamily A hA eta heta)] with k hk
  obtain ⟨Tplus, hTplus, hTplusT, hTplusT₀, hN⟩ := hk
  obtain ⟨N⟩ := hN
  refine ⟨Tplus, hTplus, hTplusT, hTplusT₀, ⟨{ N with
    noncollapsed := fun s hs x hx =>
      (N.noncollapsed s hs x hx).mono_kappa hkappa |>.mono_radius hr₀ }⟩⟩

end PoincareConjecture.M30

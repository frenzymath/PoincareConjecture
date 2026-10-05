import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Assembly.LongSlabService
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.BackwardLimit.BackwardGeneralizedConvergence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Noncollapse.SourceVolumeAtPoint
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Universe.OutputFiniteNoncollapse
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.Noncollapse

/-!
# Retaining the source noncollapse certificate

The generalized convergence record intentionally contains only the geometric
comparison data needed by the compactness assembly.  The long-slab input has
more information: every finite slab also carries the scale-bounded volume
certificate at every displayed source point.  This wrapper keeps that data
next to a selected convergence witness so a later ordinary-volume transport
argument can use the same subsequence and source cylinders.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A generalized convergence witness together with the finite-slab source
noncollapse family from the long input.  The source field is deliberately
stated before any limit transport: it retains the original moving carriers,
the endpoint-compatible slab, and the exact `kappa` and `r₀` constants. -/
structure GeneralizedBlowupConvergenceWithSourceNoncollapse
    (S : GeneralizedBlowupSequence.{u}) (kappa r₀ : ℝ) (T₀ : ℝ≥0∞) where
  convergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)
  source : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)

/-- The slab service can be attached to any already selected generalized
convergence witness without changing the witness or its subsequence. -/
def generalizedConvergenceWithSourceNoncollapse_of_slabService
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongSlabControlService S kappa r₀ T₀)
    (L : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) :
    GeneralizedBlowupConvergenceWithSourceNoncollapse S kappa r₀ T₀ := by
  exact {
    convergence := L
    source := fun T hT hTT => H.noncollapsedBounds T hT hTT }

/-- The source certificate remains valid after passing to the convergence
subsequence.  This small filter adapter is useful when the ordinary source
family is indexed by the selected limit sequence. -/
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

/-- The subsequence certificate may be weakened before a source ball is
shrunk: lowering the constant and the permitted radius range preserves the
same controlled cylinder and its endpoint data. -/
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

end PoincareMT.M30

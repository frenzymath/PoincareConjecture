import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.FiniteSlab.FiniteSlabControlled
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.BackwardLimit.BackwardGeneralizedConvergence

/-!
# The explicit long-slab control service

Claims 11.5--11.7 provide a common curvature and negative-defect bound on a
strictly shorter closed slab inside each supplied finite-horizon cylinder.
This file records that obligation and forwards it to the audited expanding
source assembly.  The service is a Prop interface; it has no local
inhabitant until those claims are established or supplied by a lower module.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- Curvature and defect bounds on shorter closed subslabs of the finite
horizon inputs.  The threshold may depend on the radius and defect, while the
coefficient `B` is chosen before those two parameters. -/
structure M30LongSlabControlService
    (S : GeneralizedBlowupSequence.{u}) (kappa r₀ : ℝ) (T₀ : ℝ≥0∞) : Prop where
  bounds : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ ∃ hTplus : T < Tplus,
          ENNReal.ofReal Tplus < T₀ ∧
          ∃ e : M30FiniteHorizonSlab S k A Tplus kappa r₀,
            (∀ s (hs : s ∈ Icc (-T) 0)
              (x : ((S.flow k).slice (S.base k).1).carrier),
              x ∈ S.baseBall k A →
              |(S.flow k).curvatureNorm
                ((FiniteHorizonSlab.closedEmbedding e hTplus).pointMap s hs x)| ≤
                B * S.scale k) ∧
            (∀ s (hs : s ∈ Icc (-T) 0)
              (x : ((S.flow k).slice (S.base k).1).carrier),
              x ∈ S.baseBall k A →
              ((S.flow k).connection
                ((FiniteHorizonSlab.closedEmbedding e hTplus).pointMap
                  s hs x).1).negativeCurvaturePart
                ((FiniteHorizonSlab.closedEmbedding e hTplus).pointMap s hs x).2 ≤
                eta * S.scale k)

/-- The slab service also exposes the projected cylinder family consumed by
the geometric convergence assembly.  Keeping this projection next to the
source certificate avoids repeating the endpoint restriction at each call
site. -/
theorem M30LongSlabControlService.controlledBounds
    {S : GeneralizedBlowupSequence.{u}} {κ r : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongSlabControlService S κ r T₀)
    (T : ℝ) (hT : 0 < T) (hTT : ENNReal.ofReal T < T₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (ControlledBlowupCylinder S k A T B eta) := by
  obtain ⟨B, hB, hfamily⟩ := H.bounds T hT hTT
  refine ⟨B, hB, ?_⟩
  intro A hA eta heta
  filter_upwards [hfamily A hA eta heta] with k hk
  obtain ⟨Tplus, hTplusPos, hTplusT, hTplusT₀, e, hcurv, hdefect⟩ := hk
  exact ⟨Tplus, hTplusPos, hTplusT, hTplusT₀,
    ⟨controlledCylinderOfFiniteHorizonSlab e hTplusT hcurv hdefect⟩⟩

/-- The same slab service can expose the source noncollapse certificate when
the later volume-transfer assembly needs it. -/
theorem M30LongSlabControlService.noncollapsedBounds
    {S : GeneralizedBlowupSequence.{u}} {κ r : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongSlabControlService S κ r T₀)
    (T : ℝ) (hT : 0 < T) (hTT : ENNReal.ofReal T < T₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        ∃ Tplus : ℝ, 0 < Tplus ∧ T < Tplus ∧
          ENNReal.ofReal Tplus < T₀ ∧
          Nonempty (NoncollapsedControlledBlowupCylinder S k A T B eta κ r) := by
  obtain ⟨B, hB, hfamily⟩ := H.bounds T hT hTT
  refine ⟨B, hB, ?_⟩
  intro A hA eta heta
  filter_upwards [hfamily A hA eta heta] with k hk
  obtain ⟨Tplus, hTplusPos, hTplusT, hTplusT₀, e, hcurv, hdefect⟩ := hk
  exact ⟨Tplus, hTplusPos, hTplusT, hTplusT₀,
    ⟨noncollapsedControlledCylinderOfFiniteHorizonSlab e hTplusT hcurv hdefect⟩⟩

/-- The explicit long-slab service supplies the controlled-cylinder premise
needed by the full backward generalized-convergence theorem. -/
theorem exists_backward_generalizedBlowupConvergence_of_longSlabService
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u}) {T₀ : ℝ≥0∞} {kappa r₀ rho v : ℝ}
    (hT₀ : 0 < T₀) (hrho : 0 < rho) (hv : 0 < v)
    (hcompact : BlowupBaseBallsCompact S)
    (H : M30LongSlabControlService S kappa r₀ T₀)
    (hvolume : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho)) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  refine exists_backward_generalizedBlowupConvergence hShi hMixed hFlow hSlice S hT₀
    hrho hv hcompact ?_ hvolume
  intro T hT hTT
  obtain ⟨B, hB, hfamily⟩ := H.bounds T hT hTT
  refine ⟨B, hB, ?_⟩
  intro A hA eta heta
  filter_upwards [hfamily A hA eta heta] with k hk
  obtain ⟨Tplus, hTplusPos, hTplusT, hTplusT₀, e, hcurv, hdefect⟩ := hk
  exact ⟨controlledCylinderOfFiniteHorizonSlab e hTplusT hcurv hdefect⟩

end PoincareMT.M30

import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabControlled
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardGeneralizedConvergence











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30




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

end PoincareConjecture.M30

import PoincareConjecture.Proofs.M30.Thm11_8.CofinalSourceDiagonal
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardGeneralizedConvergence















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30




theorem exists_backward_convergence_of_finite_prefixes
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {T0 : ℝ≥0∞} {rho v : ℝ}
    (hT0 : 0 < T0) (hrho : 0 < rho) (hv : 0 < v)
    (hcompact : BlowupBaseBallsCompact S)
    (hvolume : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho))
    (T B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < T0 → ∃ j, t ≤ T j)
    (hprefix : ∀ n : ℕ, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ j : ℕ, j ≤ n → ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (phi k) A (T j) (B j) eta)) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T0)) := by
  obtain ⟨sigma, hsigma, hC⟩ :=
    exists_reindexed_diagonal_controlled_cylinders S T B hprefix
  let S' := reindexedBlowupSequence S sigma hsigma
  have hcompact' : BlowupBaseBallsCompact S' :=
    fun A hA => hsigma.tendsto_atTop.eventually (hcompact A hA)
  have hvolume' : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S'.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S'.flow k).metric (S'.base k).1)
          (S'.baseBall k rho) := hsigma.tendsto_atTop.eventually hvolume
  have hcyl : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < T0 →
      ∃ b : ℝ, 0 ≤ b ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S' k A t b eta) := by
    intro t ht htT0
    obtain ⟨j, hj⟩ := hcofinal t ht htT0
    refine ⟨B j, hB j, ?_⟩
    intro A hA eta heta
    filter_upwards [hC j A hA eta heta] with k hk
    obtain ⟨E⟩ := hk
    have hI : Icc (-t) 0 ⊆ Icc (-(T j)) 0 :=
      Icc_subset_Icc (neg_le_neg hj) le_rfl
    exact ⟨{
      embedding := Cylinder.restrict E.embedding hI Subset.rfl
      zero_identity := fun hs x hx => E.zero_identity (hI hs) x hx
      curvature_bound := fun s hs x hx => E.curvature_bound s (hI hs) x hx
      negative_curvature_bound := fun s hs x hx =>
        E.negative_curvature_bound s (hI hs) x hx }⟩
  obtain ⟨G⟩ := exists_backward_generalizedBlowupConvergence
    hShi hMixed hFlow hSlice S' hT0 hrho hv hcompact' hcyl hvolume'
  exact ⟨convergenceOfReindexed G⟩

end PoincareConjecture.M30

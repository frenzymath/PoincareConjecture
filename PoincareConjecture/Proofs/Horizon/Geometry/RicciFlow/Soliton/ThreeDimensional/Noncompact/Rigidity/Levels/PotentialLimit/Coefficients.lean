import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.CoefficientBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.SpacetimeJets
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPrecompose








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

def normalizedPotentialSpacetimeCoefficients (z : L.limitCarrier.carrier) (k : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  fun p => (G.unscaledSourceFlow.shrink.metric p.1).pullbackCoefficients
    (L.embedding k ∘ (extChartAt (𝓡 3) z).symm) p.2

private def coefficientWindow := AncientPointedGeometricConvergence.window
  (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
  (J := fun _ => Iio (1 : ℝ)) (T := 1)
  (fun _ => G.unscaledSourceFlow.shrink) L
  (a := -1) (b := 1 / 2) (by norm_num) (by norm_num) 0
  (by intro k t ht; exact ht.2.trans (by norm_num : (1 / 2 : ℝ) < 1))

private theorem normalizedPotentialSpacetimeCoefficients_eq_window
    (z : L.limitCarrier.carrier) (k : ℕ) :
    G.normalizedPotentialSpacetimeCoefficients L z k =
      (G.coefficientWindow L).spatialSpacetimeCoefficients z k := by
  unfold normalizedPotentialSpacetimeCoefficients coefficientWindow
    PointedGeometricConvergence.spatialSpacetimeCoefficients
  simp only [AncientPointedGeometricConvergence.window,
    sourceWindowSequence, Nat.add_zero]
  rfl

theorem normalizedPotentialSpacetimeCoefficients_locally_smooth
    (z : L.limitCarrier.carrier) :
    ∀ p ∈ Ioo (-1 : ℝ) (1 / 2) ×ˢ (extChartAt (𝓡 3) z).target,
      ∃ U, IsOpen U ∧ p ∈ U ∧ ∀ᶠ k in atTop,
        ContDiffOn ℝ ∞ (G.normalizedPotentialSpacetimeCoefficients L z k) U := by
  simp_rw [G.normalizedPotentialSpacetimeCoefficients_eq_window L z]
  exact (G.coefficientWindow L).locally_eventually_contDiff_spatialSpacetimeCoefficients
    (by norm_num) z

theorem normalizedPotentialSpacetimeCoefficients_tendsto_jets
    (z : L.limitCarrier.carrier) (r : ℕ)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKt : K ⊆ Ioo (-1 : ℝ) (1 / 2) ×ˢ (extChartAt (𝓡 3) z).target) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (G.normalizedPotentialSpacetimeCoefficients L z k))
      (iteratedFDeriv ℝ r (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (L.limitFlow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) z).symm p.2))
      atTop K := by
  simp_rw [G.normalizedPotentialSpacetimeCoefficients_eq_window L z]
  exact (G.coefficientWindow L).tendstoUniformlyOn_spatialSpacetimeCoefficients_jets
    (by norm_num) z r hK hKt

theorem normalizedPotentialCoefficients_smooth_convergence
    (z : L.limitCarrier.carrier) :
    Poincare.Analysis.Calculus.LocallyEventuallyContDiff
      (extChartAt (𝓡 3) z).target
      (fun k x => G.normalizedPotentialSpacetimeCoefficients L z k (0, x)) ∧
    ∀ r K, IsCompact K → K ⊆ (extChartAt (𝓡 3) z).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r
          (fun x => G.normalizedPotentialSpacetimeCoefficients L z k (0, x)))
        (iteratedFDeriv ℝ r
          ((L.limitFlow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) z).symm)) atTop K := by
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (L.limitFlow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) z).symm p.2)
      (Ioo (-1 : ℝ) (1 / 2) ×ˢ (extChartAt (𝓡 3) z).target) := by
    intro p hp
    exact (L.limitFlow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Iio
      ((contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hp.2))
      (hp.1.2.trans (by norm_num))).contDiffWithinAt
  obtain ⟨hlocal, hjet⟩ :=
    Poincare.Analysis.Calculus.smooth_convergence_comp_continuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
      (isOpen_Ioo.prod (isOpen_extChartAt_target z)) hs
      (G.normalizedPotentialSpacetimeCoefficients_locally_smooth L z)
      (fun r K hK hKt => G.normalizedPotentialSpacetimeCoefficients_tendsto_jets L z r hK hKt)
  have hpre : (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) ⁻¹'
      (Ioo (-1 : ℝ) (1 / 2) ×ˢ (extChartAt (𝓡 3) z).target) =
      (extChartAt (𝓡 3) z).target := by ext x; simp
  rw [hpre] at hlocal hjet
  exact ⟨Poincare.Analysis.Calculus.locallyEventuallyContDiff_of_local hlocal, hjet⟩

end PoincareConjecture.ShrinkingSolitonFlow

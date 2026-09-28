import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.NullSplitting
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem bounded_curvature_or_strictlyPositiveSectionalCurvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (t : ℝ) (ht : t < 0) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) ∨
    (L.convergence.limit.flow.connection t).StrictlyPositiveSectionalCurvature := by
  by_cases hpos :
      (L.convergence.limit.flow.connection t).StrictlyPositiveSectionalCurvature
  · exact Or.inr hpos
  · apply Or.inl
    dsimp only [LeviCivitaData.StrictlyPositiveSectionalCurvature] at hpos
    push Not at hpos
    obtain ⟨x, v, w, hv, hw, hvw, hnonpos⟩ := hpos
    have heq : (L.convergence.limit.flow.connection t).sectionalCurvature x v w =
        (L.convergence.limit.flow.connection t).curvatureTensor x v w v w := by
      simp only [LeviCivitaData.sectionalCurvature, hv, hw, hvw, one_mul,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one]
    rw [heq] at hnonpos
    have hnonneg := LeviCivitaData.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      (L.convergence.limit.flow.connection t) x
        (L.convergence.limit.nonnegative_curvature_operator t ht x) v w
    exact L.bounded_curvature_of_null_plane hC t ht x v w hv hw hvw
      (le_antisymm hnonpos hnonneg)

theorem strictlyPositiveSectionalCurvature_of_unbounded_scalarCurvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (t : ℝ) (ht : t < 0)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t).scalarCurvature)) :
    (L.convergence.limit.flow.connection t).StrictlyPositiveSectionalCurvature := by
  rcases L.bounded_curvature_or_strictlyPositiveSectionalCurvature hC t ht with hbound | hpos
  · exfalso
    exact hunbounded
      ((L.convergence.limit.bddAbove_scalarCurvature_iff_bounded_curvature hC t ht).mpr hbound)
  · exact hpos

theorem ulift_strictlyPositiveSectionalCurvature_of_unbounded_scalarCurvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (t : ℝ) (ht : t < 0)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t).scalarCurvature)) :
    LeviCivitaData.StrictlyPositiveSectionalCurvature
      ((L.convergence.limit.flow.ulift :
        RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).connection t) := by
  let F := L.convergence.limit.flow
  let e : (ULift.{u} L.convergence.limit.carrier.carrier) ≃ₘ⟮𝓡 3, 𝓡 3⟯
      L.convergence.limit.carrier.carrier :=
    Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier
  have hpos := L.strictlyPositiveSectionalCurvature_of_unbounded_scalarCurvature hC t ht hunbounded
  intro x v w hv hw hvw
  change ((F.pullbackDiffeomorph e).connection t).sectionalCurvature x v w > 0
  rw [((F.pullbackDiffeomorph e).connection t).sectionalCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)]
  exact hpos (e x) _ _ hv hw hvw

end PoincareConjecture.AncientAsymptoticSolitonLimitData

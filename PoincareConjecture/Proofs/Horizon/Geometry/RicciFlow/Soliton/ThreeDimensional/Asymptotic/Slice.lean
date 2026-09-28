import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.LimitNoncollapse

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem contMDiff_potential_slice (L : AncientAsymptoticSolitonLimitData S)
    (t : ℝ) (ht : t < 0) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => L.potential (x, t)) := by
  have hslice : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓘(ℝ, ℝ))) ∞
      (fun x : L.convergence.limit.carrier.carrier => (x, t)) :=
    contMDiff_id.prodMk contMDiff_const
  have h := L.potential_smooth.comp hslice.contMDiffOn
    (show MapsTo (fun x : L.convergence.limit.carrier.carrier => (x, t))
      univ (univ ×ˢ Iio 0) from fun x _ => ⟨mem_univ x, ht⟩)
  exact contMDiffOn_univ.mp h

noncomputable def shrinkingSolitonData
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection (-1)).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    GradientShrinkingSolitonData 3 L.convergence.limit.carrier.carrier := by
  letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  refine
    { metric := L.convergence.limit.flow.metric (-1)
      connection := L.convergence.limit.flow.connection (-1)
      dimension := Or.inr rfl
      complete := L.convergence.limit.complete (-1) (by norm_num)
      nonflat := L.nonflat_at (-1) (by norm_num)
      nonnegative_curvature := L.convergence.limit.nonnegative_curvature_operator (-1) (by norm_num)
      bounded_curvature := hbound
      kappa := K.kappa / 729
      kappa_pos := div_pos K.kappa_pos (by norm_num)
      kappa_noncollapsed := L.convergence.limit.metricKappaNoncollapsed_of_scalar_derivative_nonnegative
        hC K.kappa_pos L.kappa_noncollapsed L.scalar_curvature_nonnegative_time_derivative
        (by norm_num)
      potential := fun x => L.potential (x, -1)
      potential_C2 := ?_
      soliton_equation := ?_ }
  · exact (L.contMDiff_potential_slice (-1) (by norm_num)).of_le (by norm_cast)
  · intro x v w
    have h := L.soliton_equation (-1) (by norm_num) x v w
    norm_num at h
    linarith

end PoincareConjecture.AncientAsymptoticSolitonLimitData

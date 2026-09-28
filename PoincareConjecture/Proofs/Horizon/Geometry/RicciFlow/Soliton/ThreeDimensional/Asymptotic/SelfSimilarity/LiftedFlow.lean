import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  uliftSecondCountable uliftConnected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

@[simp] theorem normalizedShrinkingSolitonData_metric_neg_one
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection (-1)).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    (L.normalizedShrinkingSolitonData hC (-1) (by norm_num) hbound).metric =
      (L.convergence.limit.flow.ulift :
        RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).metric (-1) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  change rescaledMetric _ |(-1 : ℝ)|⁻¹ (by norm_num) = _
  simp only [abs_neg, abs_one, inv_one, rescaledMetric, one_smul]


theorem nonempty_homotheticMetricSlice_ulift
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (t : ℝ) (ht : t < 0) :
    Nonempty (HomotheticMetricSlice
      ((L.convergence.limit.flow.ulift :
        RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).metric (-1))
      (L.convergence.limit.flow.ulift.metric t) |t|) := by
  obtain ⟨d⟩ := L.nonempty_homotheticMetricSlice hC hbound t ht
  let F := L.convergence.limit.flow
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier
  let k := (e.trans d.map).trans e.symm
  refine ⟨{ map := k, inner_eq := ?_ }⟩
  intro x v w
  have hcomp : e ∘ k = d.map ∘ e := by
    funext y
    exact e.apply_symm_apply (d.map (e y))
  have hd (v : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e (k x) (mfderiv (𝓡 3) (𝓡 3) k x v) =
        mfderiv (𝓡 3) (𝓡 3) d.map (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
    have h : mfderiv (𝓡 3) (𝓡 3) (e ∘ k) x =
        mfderiv (𝓡 3) (𝓡 3) (d.map ∘ e) x := by rw [hcomp]
    rw [mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
      (k.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x (d.map.contMDiff.mdifferentiable (by simp) _)
        (e.contMDiff.mdifferentiable (by simp) x)] at h
    exact congrArg (fun A => A v) h
  change (F.metric t).inner (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
    |t| * (F.metric (-1)).inner (e (k x))
      (mfderiv (𝓡 3) (𝓡 3) e (k x) (mfderiv (𝓡 3) (𝓡 3) k x v))
      (mfderiv (𝓡 3) (𝓡 3) e (k x) (mfderiv (𝓡 3) (𝓡 3) k x w))
  rw [hd v, hd w, show e (k x) = d.map (e x) from congrFun hcomp x]
  exact d.inner_eq (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w)



def liftedShrinkingSolitonFlow
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    ShrinkingSolitonFlow (L.normalizedShrinkingSolitonData hC (-1) (by norm_num)
      (hbound (-1) (by norm_num))) := by
  letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  refine
    { flow := L.convergence.limit.flow.ulift
      at_minus_one := (L.normalizedShrinkingSolitonData_metric_neg_one hC _).symm
      self_similar := ?_ }
  intro t ht
  rw [L.normalizedShrinkingSolitonData_metric_neg_one hC]
  exact L.nonempty_homotheticMetricSlice_ulift hC hbound t ht

@[simp] theorem liftedShrinkingSolitonFlow_flow
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    (L.liftedShrinkingSolitonFlow hC hbound).flow = L.convergence.limit.flow.ulift := rfl

end PoincareConjecture.AncientAsymptoticSolitonLimitData

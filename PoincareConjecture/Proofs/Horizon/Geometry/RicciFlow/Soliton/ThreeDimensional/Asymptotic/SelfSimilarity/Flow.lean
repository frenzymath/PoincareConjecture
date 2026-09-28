import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.Evolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.MetricIdentity











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

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}



theorem nonempty_homotheticMetricSlice
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (t : ℝ) (ht : t < 0) :
    Nonempty (HomotheticMetricSlice (L.convergence.limit.flow.metric (-1))
      (L.convergence.limit.flow.metric t) |t|) := by
  obtain ⟨E, hi, hs, hODE, _, hinv⟩ := L.exists_negative_potential_gradient_evolution hC hbound
  have hneg : (-1 : ℝ) < 0 := by norm_num
  have hslice (s : ℝ) (hs0 : s < 0) (r : ℝ) (hr : r < 0) :
      ContMDiff (𝓡 3) (𝓡 3) ∞ (E s r) := by
    apply contMDiffOn_univ.mp
    exact (hs s hs0).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x _ => ⟨hr, mem_univ x⟩)
  let Ψ : Diffeomorph (𝓡 3) (𝓡 3)
      L.convergence.limit.carrier.carrier L.convergence.limit.carrier.carrier ∞ :=
    { toFun := E (-1) t
      invFun := E t (-1)
      left_inv := (hinv (-1) hneg t ht).1
      right_inv := (hinv (-1) hneg t ht).2
      contMDiff_toFun := hslice (-1) hneg t ht
      contMDiff_invFun := hslice t ht (-1) hneg }
  refine ⟨{ map := Ψ.symm, inner_eq := ?_ }⟩
  intro x v w
  have hinverse (v : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) Ψ (Ψ.symm x)
        (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x v) = v := by
    have h := mfderiv_comp x (Ψ.contMDiff.mdifferentiable (by simp) _)
      (Ψ.symm.contMDiff.mdifferentiable (by simp) x)
    have hcomp : Ψ ∘ Ψ.symm = id := funext Ψ.apply_symm_apply
    rw [hcomp, mfderiv_id] at h
    exact congrArg (fun A => A v) h.symm
  have h := L.negativeGradient_pullback_metric (hs (-1) hneg)
    (fun r hr y => hODE (-1) hneg y r hr) (hi (-1) hneg) ht (Ψ.symm x)
    (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x v) (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x w)
  change (L.convergence.limit.flow.metric t).inner (Ψ (Ψ.symm x))
      (mfderiv (𝓡 3) (𝓡 3) Ψ (Ψ.symm x) (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x v))
      (mfderiv (𝓡 3) (𝓡 3) Ψ (Ψ.symm x) (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x w)) =
    (-t) * (L.convergence.limit.flow.metric (-1)).inner (Ψ.symm x)
      (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x v) (mfderiv (𝓡 3) (𝓡 3) Ψ.symm x w) at h
  rw [hinverse v, hinverse w, Ψ.apply_symm_apply] at h
  simpa only [abs_of_neg ht] using h



def shrinkingSolitonFlow
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    ShrinkingSolitonFlow (L.shrinkingSolitonData hC (hbound (-1) (by norm_num))) := by
  letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  exact
    { flow := L.convergence.limit.flow
      at_minus_one := rfl
      self_similar := L.nonempty_homotheticMetricSlice hC hbound }

@[simp] theorem shrinkingSolitonFlow_flow
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    (L.shrinkingSolitonFlow hC hbound).flow = L.convergence.limit.flow := rfl

end PoincareConjecture.AncientAsymptoticSolitonLimitData

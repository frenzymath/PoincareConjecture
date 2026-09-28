import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.ComponentTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly



set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.SingularTimeReference

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


noncomputable def sliceDiffeomorph (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞ where
  toFun := R.forward t ht
  invFun := R.inverse t ht
  left_inv := R.left_inverse t ht
  right_inv := R.right_inverse t ht
  contMDiff_toFun := R.forward_smooth t ht
  contMDiff_invFun := R.inverse_smooth t ht

theorem slice_metric_homothety (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) :
    MetricHomothety (R.flow.metric t) (F.metric t) (R.sliceDiffeomorph t ht) 1 := by
  intro x v w
  change (F.metric t).inner (R.forward t ht x)
    (mfderiv (𝓡 3) (𝓡 3) (R.forward t ht) x v)
    (mfderiv (𝓡 3) (𝓡 3) (R.forward t ht) x w) = 1 * (R.flow.metric t).inner x v w
  simpa only [one_mul] using R.metric_pullback t ht x v w

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



noncomputable def referenceCComponent (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) {C : ℝ}
    (N : SingularCComponent (F.metric t) (F.connection t) C) :
    SingularCComponent (R.flow.metric t) (R.flow.connection t) C :=
  N.m48_pullback (R.slice_metric_homothety t ht)
    (Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num)
      (R.slice_metric_homothety t ht)) (R.flow.connection t)

theorem referenceCComponent_carrier (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) {C : ℝ}
    (N : SingularCComponent (F.metric t) (F.connection t) C) {x : M}
    (hx : R.forward t ht x ∈ N.carrier) :
    (R.referenceCComponent t ht N).carrier = connectedComponent x := by
  change R.sliceDiffeomorph t ht ⁻¹' N.carrier = connectedComponent x
  have hc := connectedComponent_eq (N.component_eq ▸ hx)
  rw [N.component_eq, hc]
  exact (M48.preimage_connectedComponent (R.sliceDiffeomorph t ht).toHomeomorph
    (R.forward t ht x)).trans (congrArg connectedComponent (R.left_inverse t ht x))

end PoincareConjecture.SingularTimeReference

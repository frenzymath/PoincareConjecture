import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Reference








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

namespace SingularRoundComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}



def restrictToOpen (N : SingularRoundComponent g epsilon) (U : Opens M)
    (hNU : N.carrier ⊆ U) (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner (x : M) (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) = gU.inner x v w) :
    SingularRoundComponent gU epsilon := by
  have hbase : N.basepoint ∈ N.carrier := N.component_eq ▸ mem_connectedComponent
  have hforward (y : N.model.carrier) : N.forward y ∈ N.carrier :=
    N.forward_image ▸ mem_range_self y
  let j : N.model.carrier → U := fun y => ⟨N.forward y, hNU (hforward y)⟩
  have hj : ContMDiff (𝓡 3) (𝓡 3) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff U j).mp N.forward_smooth
  have hcomp : (Subtype.val : U → M) ∘ j = N.forward := rfl
  have hpull : singularMetricPullback gU j = singularMetricPullback g N.forward := by
    funext y v
    have hd := mfderiv_comp y
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (j y))
      (hj.mdifferentiable (by simp) y)
    rw [hcomp] at hd
    have hv (w : TangentSpace (𝓡 3) y) :
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) (j y)
          (mfderiv (𝓡 3) (𝓡 3) j y w) = mfderiv (𝓡 3) (𝓡 3) N.forward y w :=
      (congrArg (fun A => A w) hd).symm
    have h := hmetric (j y) (mfderiv (𝓡 3) (𝓡 3) j y (v 0))
      (mfderiv (𝓡 3) (𝓡 3) j y (v 1))
    rw [hv, hv] at h
    exact h.symm
  refine {
    epsilon_pos := N.epsilon_pos
    basepoint := ⟨N.basepoint, hNU hbase⟩
    carrier := (Subtype.val : U → M) ⁻¹' N.carrier
    component_eq := ?_
    compact := Topology.IsInducing.subtypeVal.isCompact_preimage' N.compact
      (by simpa only [Subtype.range_coe] using hNU)
    model := N.model
    model_compact := N.model_compact
    model_connected := N.model_connected
    model_metric := N.model_metric
    model_connection := N.model_connection
    model_curvature_one := N.model_curvature_one
    forward := j
    inverse := fun x => N.inverse x.val
    forward_image := ?_
    forward_openEmbedding := ?_
    forward_smooth := hj
    inverse_smooth := N.inverse_smooth.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
    left_inverse := N.left_inverse
    right_inverse := fun x hx => Subtype.ext (N.right_inverse hx)
    scale := N.scale
    scale_pos := N.scale_pos
    metric_comparison := ?_ }
  · rw [SingularRegularLimit.connectedComponent_subtype_eq_preimage
      (⟨N.basepoint, hNU hbase⟩ : U) (by simpa only [← N.component_eq] using hNU)]
    rw [N.component_eq]
    rfl
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hforward y
    · intro hx
      exact ⟨N.inverse x.val, Subtype.ext (N.right_inverse hx)⟩
  · exact Topology.IsOpenEmbedding.of_comp j U.isOpen.isOpenEmbedding_subtypeVal
      (hcomp ▸ N.forward_openEmbedding)
  · rw [hpull]
    exact N.metric_comparison

@[simp] theorem restrictToOpen_carrier (N : SingularRoundComponent g epsilon) (U : Opens M)
    (hNU : N.carrier ⊆ U) (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner (x : M) (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) = gU.inner x v w) :
    (N.restrictToOpen U hNU gU hmetric).carrier = (Subtype.val : U → M) ⁻¹' N.carrier := rfl

end SingularRoundComponent

namespace SingularTimeReference

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


def referenceRoundComponent (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) {epsilon : ℝ}
    (N : SingularRoundComponent (F.metric t) epsilon) :
    SingularRoundComponent (R.flow.metric t) epsilon :=
  N.m48_pullback (R.slice_metric_homothety t ht)

theorem referenceRoundComponent_carrier (R : SingularTimeReference F T M)
    (t : ℝ) (ht : t ∈ Ico R.tMinus T) {epsilon : ℝ}
    (N : SingularRoundComponent (F.metric t) epsilon) {x : M}
    (hx : R.forward t ht x ∈ N.carrier) :
    (R.referenceRoundComponent t ht N).carrier = connectedComponent x := by
  change R.sliceDiffeomorph t ht ⁻¹' N.carrier = connectedComponent x
  have hc := connectedComponent_eq (N.component_eq ▸ hx)
  rw [N.component_eq, hc]
  exact (M48.preimage_connectedComponent (R.sliceDiffeomorph t ht).toHomeomorph
    (R.forward t ht x)).trans (congrArg connectedComponent (R.left_inverse t ht x))

end SingularTimeReference

end PoincareConjecture

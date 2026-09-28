import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.ComponentCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace SingularTimeReference

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


theorem inverse_image_connectedComponent
    (R : SingularTimeReference F T M) (t : ℝ) (ht : t ∈ Ico R.tMinus T)
    (x : M) :
    R.inverse t ht '' connectedComponent (R.forward t ht x) = connectedComponent x := by
  let e : M ≃ₜ (F.slice t).carrier := {
    toFun := R.forward t ht
    invFun := R.inverse t ht
    left_inv := R.left_inverse t ht
    right_inv := R.right_inverse t ht
    continuous_toFun := (R.forward_smooth t ht).continuous
    continuous_invFun := (R.inverse_smooth t ht).continuous }
  change e.symm '' connectedComponent (e x) = connectedComponent x
  rw [e.symm.image_eq_preimage_symm, M48.preimage_connectedComponent]
  simp only [Homeomorph.symm_symm, e.symm_apply_apply]

end SingularTimeReference

namespace SingularRegularLimit


theorem connectedComponent_subtype_eq_preimage
    {X : Type u} [TopologicalSpace X] {U : Set X} (x : U)
    (hU : connectedComponent (x : X) ⊆ U) :
    connectedComponent x = Subtype.val ⁻¹' connectedComponent (x : X) := by
  apply subset_antisymm
  · intro y hy
    exact continuous_subtype_val.image_connectedComponent_subset x ⟨y, hy, rfl⟩
  · have hpre : IsPreconnected (Subtype.val ⁻¹' connectedComponent (x : X) : Set U) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hU]
      exact isPreconnected_connectedComponent
    exact hpre.subset_connectedComponent mem_connectedComponent

end SingularRegularLimit

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_late_cComponent_terminal_carrier
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
        ∀ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
          H.reference.forward t ht x ∈ N.carrier →
          H.reference.inverse t ht '' N.carrier = connectedComponent (x : M) ∧
          connectedComponent (x : M) ⊆ H.reference.regularLimitSet ∧
          connectedComponent x = Subtype.val ⁻¹' connectedComponent (x : M) ∧
          IsCompact (connectedComponent x) := by
  obtain ⟨A, hA, hAreg, s, hsref, hsT, hcapture⟩ :=
    H.exists_compact_cComponent_carrier_capture P04 x.property
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht hst N hxN
  have hcarrier : H.reference.inverse t ht '' N.carrier = connectedComponent (x : M) := by
    have hcomponent := connectedComponent_eq (N.component_eq ▸ hxN)
    rw [N.component_eq, hcomponent]
    exact H.reference.inverse_image_connectedComponent t ht x
  have hreg : connectedComponent (x : M) ⊆ H.reference.regularLimitSet := by
    rw [← hcarrier]
    exact subset_closure.trans ((hcapture t ht hst N hxN).trans hAreg)
  have hterminal := SingularRegularLimit.connectedComponent_subtype_eq_preimage x hreg
  refine ⟨hcarrier, hreg, hterminal, ?_⟩
  rw [hterminal]
  apply Topology.IsInducing.subtypeVal.isCompact_preimage'
  · rw [← hcarrier]
    exact N.compact.image (H.reference.inverse_smooth t ht).continuous
  · rw [Subtype.range_coe]
    exact hreg

end SingularTimeAssumptions

end PoincareConjecture

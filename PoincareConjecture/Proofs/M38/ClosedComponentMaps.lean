import PoincareConjecture.Proofs.M38.Components









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M38

attribute [local instance] SmoothClosedComponentModel.model_topology
  SmoothClosedComponentModel.model_charted SmoothClosedComponentModel.model_manifold



noncomputable def componentClosedModelDiffeomorph (S : GeneralizedSliceCarrier.{u})
    (x : S.carrier) {kind : ClosedComponentKind}
    (C : SmoothClosedComponentModel kind (connectedComponent x)) :
    Diffeomorph (𝓡 3) (𝓡 3) (componentCarrier S x).carrier C.model ∞ := by
  let forward : C.model → (componentCarrier S x).carrier :=
    fun y => ⟨C.forward y, C.forward_mem y⟩
  refine {
    toEquiv := {
      toFun := fun y => C.inverse y.1
      invFun := forward
      left_inv := ?_
      right_inv := C.right_inverse }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro y
    apply Subtype.ext
    exact C.left_inverse y.1 y.property
  · apply contMDiffOn_univ.mp
    exact C.inverse_smooth.comp
      (contMDiff_subtype_val (U := componentOpen S x)).contMDiffOn
      (fun y _ => y.property)
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen S x) forward).mp
    exact C.forward_smooth



noncomputable def projectiveCoverAlongDiffeomorph
    {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    {S : GeneralizedSliceCarrier.{u}}
    (C : StandardProjectiveSmoothCover Q)
    (d : Diffeomorph (𝓡 3) (𝓡 3) S.carrier Q ∞) :
    StandardProjectiveSmoothCover S.carrier where
  cover := d.symm ∘ C.cover
  surjective := d.symm.surjective.comp C.surjective
  fibers := fun x y => by
    change d.symm (C.cover x) = d.symm (C.cover y) ↔ _
    exact d.symm.injective.eq_iff.trans (C.fibers x y)
  local_diffeomorph := fun x =>
    (C.local_diffeomorph x).comp (𝓡 3) S.carrier (d.symm.isLocalDiffeomorph (C.cover x))

end PoincareConjecture.M38

import PoincareConjecture.Proofs.M38.ComponentSpaceforms









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M38



noncomputable def componentRoundDiffeomorph (S : GeneralizedSliceCarrier.{u})
    {g : RiemannianMetric 3 S.carrier} {epsilon : ℝ}
    (Q : SingularRoundComponent g epsilon) (x : S.carrier)
    (hcarrier : Q.carrier = connectedComponent x) :
    Diffeomorph (𝓡 3) (𝓡 3) (componentCarrier S x).carrier Q.model.carrier ∞ := by
  let forward : Q.model.carrier → (componentCarrier S x).carrier := fun y =>
    ⟨Q.forward y, hcarrier.subset (Q.forward_image.subset (Set.mem_range_self y))⟩
  refine {
    toEquiv := {
      toFun := fun y => Q.inverse y.1
      invFun := forward
      left_inv := ?_
      right_inv := Q.left_inverse }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro y
    apply Subtype.ext
    exact Q.right_inverse (hcarrier.symm.subset y.property)
  · apply contMDiffOn_univ.mp
    exact Q.inverse_smooth.comp
      (contMDiff_subtype_val (U := componentOpen S x)).contMDiffOn
      (fun y _ => hcarrier.symm.subset y.property)
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen S x) forward).mp
    exact Q.forward_smooth



noncomputable def roundSpaceformOnComponent (S : GeneralizedSliceCarrier.{u})
    {g : RiemannianMetric 3 S.carrier} {epsilon : ℝ}
    (Q : SingularRoundComponent g epsilon) (x : S.carrier)
    (hcarrier : Q.carrier = connectedComponent x) :
    SurgeryPositiveSpaceform (componentCarrier S x) := by
  apply spaceformAlongDiffeomorph (componentCarrier S x) Q.model_metric
    Q.model_connection (componentRoundDiffeomorph S Q x hcarrier) ?_
    (componentCarrier_connected S x) ?_
  · change IsCompact (Set.univ : Set (connectedComponent x))
    exact isCompact_univ_iff.mpr
      (isCompact_iff_compactSpace.mp (hcarrier ▸ Q.compact))
  · exact ⟨1, zero_lt_one, fun y u v hu hv huv =>
      Q.model_curvature_one y u v ⟨hu, hv, huv⟩⟩

end PoincareConjecture.M38

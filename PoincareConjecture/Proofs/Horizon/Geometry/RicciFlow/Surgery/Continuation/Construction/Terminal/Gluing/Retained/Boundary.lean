import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Identification








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)
  (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)

include hUn in
omit [Countable ι] in
theorem negativeHalf_subset_closure_retained (i : ι) :
    ((I i).negativeHalf : Set S.carrier) ⊆ closure (U : Set S.carrier) := by
  apply Subset.trans ?_ subset_closure
  rw [← hUn i]
  exact inter_subset_left

include hUn in
omit [Countable ι] in
theorem positiveHalf_disjoint_closure_retained (i : ι) :
    Disjoint ((I i).neck.region 0 (I i).neck.epsilon⁻¹)
      (closure (U : Set S.carrier)) := by
  apply Disjoint.closure_right ?_ (MetricSurgery.neck_region_isOpen _ _ _)
  apply Set.disjoint_left.mpr
  intro x hx hxU
  have hneg : x ∈ (I i).negativeHalf := by
    change x ∈ ((I i).negativeHalf : Set S.carrier)
    rw [← hUn i]
    exact ⟨hxU, hx.1⟩
  exact lt_asymm hx.2.1 hneg.2.2

include hneck hUn in
theorem retainedMap_centralSphere (i : ι) :
    retainedMap I R U hU hd hc '' (I i).neck.central_sphere =
      frontier (capChart I R U hU hd hc i).carrier := by
  rw [capChart_frontier, ← image_comp]
  apply image_congr
  intro x hx
  exact retainedMap_apply_collar I R U hU hd hc hneck hUn i x
    ((I i).centralSphere_subset_retainedCollar hx)

include hneck hUn in
theorem retainedMap_negativeHalf (i : ι) (x : S.carrier)
    (hx : x ∈ (I i).negativeHalf) :
    retainedMap I R U hU hd hc x = capInclusion I R U hU hd hc i ((R i).collapse x) :=
  retainedMap_apply_collar I R U hU hd hc hneck hUn i x
    ((I i).negativeHalf_subset_retainedCollar hx)

end PoincareConjecture.Surgery.Terminal.Gluing

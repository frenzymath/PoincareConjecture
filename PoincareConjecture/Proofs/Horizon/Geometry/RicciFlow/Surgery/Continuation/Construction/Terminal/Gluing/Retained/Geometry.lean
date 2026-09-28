import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Embedding









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology Filter
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

include hneck hUn in
theorem retainedMap_metric_retained (x : U) (v w : TangentSpace (𝓡 3) x.val) :
    (cutMetric I R U hU hd hc).inner (retainedMap I R U hU hd hc x.val)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x.val v)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x.val w) = g.inner x.val v w := by
  let hv := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U x
  let e := hv.mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨a, ha⟩ := e.surjective v
  obtain ⟨b, hb⟩ := e.surjective w
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → S.carrier) x a = v at ha
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → S.carrier) x b = w at hb
  have heq : retainedMap I R U hU hd hc ∘ (Subtype.val : U → S.carrier) =
      retainedInclusion I R U hU hd hc :=
    funext (retainedMap_apply_retained I R U hU hd hc hneck hUn)
  have hm := (retainedMap_localDiffeomorphAt I R U hU hd hc hneck hUn x.val
    (retainedPieceOpen_subset_neighborhood I U none x.property)).mdifferentiableAt (by simp)
  have hder (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (retainedInclusion I R U hU hd hc) x z =
        mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → S.carrier) x z) := by
    rw [← heq]
    exact mfderiv_comp_apply x hm (hv.mdifferentiableAt (by simp)) z
  erw [← ha, ← hb, ← hder a, ← hder b,
    retainedMap_apply_retained I R U hU hd hc hneck hUn x]
  exact retainedInclusion_metric I R U hU hd hc x a b

include hneck hUn in
theorem retainedMap_metric_collar (i : ι) (x : S.carrier)
    (hx : x ∈ ((I i).negativeHalf : Set S.carrier) ∪ (I i).neck.central_sphere)
    (v w : TangentSpace (𝓡 3) x) :
    (cutMetric I R U hU hd hc).inner (retainedMap I R U hU hd hc x)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x v)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x w) = g.inner x v w := by
  have hxC : x ∈ (I i).retainedCollar := hx.elim
    (fun h => (I i).negativeHalf_subset_retainedCollar h)
    (fun h => (I i).centralSphere_subset_retainedCollar h)
  have heq : retainedMap I R U hU hd hc =ᶠ[𝓝 x]
      capInclusion I R U hU hd hc i ∘ (R i).collapse := by
    filter_upwards [(I i).retainedCollar.isOpen.mem_nhds hxC] with y hy
    exact retainedMap_apply_collar I R U hU hd hc hneck hUn i y hy
  have hdR := ((R i).retained_smooth x hxC).contMDiffAt
    ((I i).retainedCollar.isOpen.mem_nhds hxC)
  have hder (z : TangentSpace (𝓡 3) x) := mfderiv_comp_apply x
    ((capInclusion_localDiffeomorph I R U hU hd hc i _).mdifferentiableAt (by simp))
    (hdR.mdifferentiableAt (by simp)) z
  erw [heq.mfderiv_eq, hder v, hder w,
    retainedMap_apply_collar I R U hU hd hc hneck hUn i x hxC,
    capInclusion_metric]
  exact (R i).retained_metric x hx v w

variable (hfront : frontier (U : Set S.carrier) ⊆ ⋃ i, (I i).neck.central_sphere)

include hfront in
omit [Countable ι] in
theorem closure_retained_subset_neighborhood :
    closure (U : Set S.carrier) ⊆ retainedNeighborhood I U := by
  intro x hx
  by_cases hxU : x ∈ U
  · exact retainedPieceOpen_subset_neighborhood I U none hxU
  · have hxf : x ∈ frontier (U : Set S.carrier) := by
      rw [frontier, U.isOpen.interior_eq]
      exact ⟨hx, hxU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hxf)
    exact retainedPieceOpen_subset_neighborhood I U (some i)
      ((I i).centralSphere_subset_retainedCollar hi)


def retainedRegionEquivalence : SurgeryRegionEquivalence S (cutCarrier I R U hU hd hc)
    (closure (U : Set S.carrier))
    (retainedMap I R U hU hd hc '' closure (U : Set S.carrier)) where
  map := retainedMap I R U hU hd hc
  inverse := retainedInverse I R U hU hd hc
  map_image := rfl
  inverse_image := by
    let : Nonempty S.carrier := hU.map Subtype.val
    exact (retainedMap_injOn I R U hU hd hc hneck hUn).invFunOn_image
      (closure_retained_subset_neighborhood I U hfront)
  left_inverse := fun _ hx => retainedInverse_left I R U hU hd hc hneck hUn _
    (closure_retained_subset_neighborhood I U hfront hx)
  right_inverse := fun _ hy => retainedInverse_right I R U hU hd hc _
    (image_mono (closure_retained_subset_neighborhood I U hfront) hy)
  map_smooth := (retainedMap_smooth I R U hU hd hc hneck hUn).mono
    (closure_retained_subset_neighborhood I U hfront)
  inverse_smooth := (retainedInverse_smooth I R U hU hd hc hneck hUn).mono
    (image_mono (closure_retained_subset_neighborhood I U hfront))

include hneck hUn hfront in
theorem retainedMap_metric (x : S.carrier) (hx : x ∈ closure (U : Set S.carrier))
    (v w : TangentSpace (𝓡 3) x) :
    (cutMetric I R U hU hd hc).inner (retainedMap I R U hU hd hc x)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x v)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc) x w) = g.inner x v w := by
  by_cases hxU : x ∈ U
  · exact retainedMap_metric_retained I R U hU hd hc hneck hUn ⟨x, hxU⟩ v w
  · have hxf : x ∈ frontier (U : Set S.carrier) := by
      rw [frontier, U.isOpen.interior_eq]
      exact ⟨hx, hxU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hxf)
    exact retainedMap_metric_collar I R U hU hd hc hneck hUn i x (Or.inr hi) v w

include hneck hUn hfront in
theorem retainedMap_image_compact (hcompact : IsCompact (closure (U : Set S.carrier))) :
    IsCompact (retainedMap I R U hU hd hc '' closure (U : Set S.carrier)) :=
  hcompact.image_of_continuousOn ((retainedRegionEquivalence I R U hU hd hc hneck hUn hfront).map_smooth.continuousOn)

end PoincareConjecture.Surgery.Terminal.Gluing

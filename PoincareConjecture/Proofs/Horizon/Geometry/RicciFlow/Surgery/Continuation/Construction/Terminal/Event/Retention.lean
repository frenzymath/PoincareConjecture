import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Regions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Boundary

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S A : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)
  (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)
  (hfront : frontier (U : Set S.carrier) ⊆ ⋃ i, (I i).neck.central_sphere)
  {Ω : Set A.carrier} (L : SurgeryRegionEquivalence A S Ω univ)

def referenceRetained : Set A.carrier := L.inverse '' closure (U : Set S.carrier)

theorem referenceRetained_subset : referenceRetained U L ⊆ Ω := by
  rintro _ ⟨x, _, rfl⟩
  exact L.symm.mapsTo (mem_univ x)

theorem referenceRetained_compact (hcompact : IsCompact (closure (U : Set S.carrier))) :
    IsCompact (referenceRetained U L) :=
  hcompact.image (continuousOn_univ.mp L.inverse_smooth.continuousOn)

theorem referenceRetained_image : L.map '' referenceRetained U L = closure (U : Set S.carrier) :=
  (L.symm.restrict (closure (U : Set S.carrier)) (subset_univ _)).symm.map_image

def referenceRetention :
    SurgeryRegionEquivalence A (cutCarrier I R U hU hd hc) (referenceRetained U L)
      (retainedMap I R U hU hd hc '' closure (U : Set S.carrier)) :=
  (L.symm.restrict (closure (U : Set S.carrier)) (subset_univ _)).symm.trans
    (retainedRegionEquivalence I R U hU hd hc hneck hUn hfront)

@[simp] theorem referenceRetention_map (x : A.carrier) :
    (referenceRetention I R U hU hd hc hneck hUn hfront L).map x =
      retainedMap I R U hU hd hc (L.map x) := rfl

include R hU hd hc hneck hUn hfront in
theorem referenceRetained_interior :
    interior (referenceRetained U L) = L.inverse '' (U : Set S.carrier) := by
  have he := (L.symm.restrict (closure (U : Set S.carrier)) (subset_univ _)).image_interior
  change L.inverse '' interior (closure (U : Set S.carrier)) =
    interior (referenceRetained U L) at he
  rw [interior_closure_retained I R U hU hd hc hneck hUn hfront] at he
  exact he.symm

include R hU hd hc hneck hUn hfront in
theorem referenceRetained_frontier (hcompact : IsCompact (closure (U : Set S.carrier))) :
    frontier (referenceRetained U L) = ⋃ i, L.inverse '' (I i).neck.central_sphere := by
  have he := (L.symm.restrict (closure (U : Set S.carrier)) (subset_univ _)).image_frontier
    isClosed_closure (referenceRetained_compact U L hcompact).isClosed
  change L.inverse '' frontier (closure (U : Set S.carrier)) =
    frontier (referenceRetained U L) at he
  rw [frontier_closure_retained I R U hU hd hc hneck hUn hfront, image_iUnion] at he
  exact he.symm

theorem referenceRetention_boundary (i : ι) :
    (referenceRetention I R U hU hd hc hneck hUn hfront L).map ''
      (L.inverse '' (I i).neck.central_sphere) =
        frontier (capChart I R U hU hd hc i).carrier := by
  rw [← image_comp]
  have he : (referenceRetention I R U hU hd hc hneck hUn hfront L).map ∘ L.inverse =
      retainedMap I R U hU hd hc := by
    funext x
    change retainedMap I R U hU hd hc (L.map (L.inverse x)) = _
    rw [L.right_inverse (mem_univ x)]
  rw [he, retainedMap_centralSphere I R U hU hd hc hneck hUn]

include hUn in
theorem referenceRetained_negative (i : ι) :
    ((I i).negativeHalf : Set S.carrier) ⊆ L.map '' referenceRetained U L := by
  rw [referenceRetained_image]
  exact negativeHalf_subset_closure_retained I U hUn i

include hUn in
theorem referenceRetained_positive (i : ι) :
    Disjoint ((I i).neck.region 0 (I i).neck.epsilon⁻¹)
      (L.map '' referenceRetained U L) := by
  rw [referenceRetained_image]
  exact positiveHalf_disjoint_closure_retained I U hUn i

theorem referenceRetention_local (i : ι) (x : S.carrier) (hx : x ∈ (I i).negativeHalf) :
    capInclusion I R U hU hd hc i ((R i).collapse x) =
      (referenceRetention I R U hU hd hc hneck hUn hfront L).map (L.inverse x) := by
  rw [referenceRetention_map, L.right_inverse (mem_univ x)]
  exact (retainedMap_negativeHalf I R U hU hd hc hneck hUn i x hx).symm

theorem referenceRetention_metric (hΩ : IsOpen Ω) (x : A.carrier)
    (hx : x ∈ referenceRetained U L) (v w : TangentSpace (𝓡 3) x) :
    (cutMetric I R U hU hd hc).inner
      ((referenceRetention I R U hU hd hc hneck hUn hfront L).map x)
      (mfderiv (𝓡 3) (𝓡 3)
        (referenceRetention I R U hU hd hc hneck hUn hfront L).map x v)
      (mfderiv (𝓡 3) (𝓡 3)
        (referenceRetention I R U hU hd hc hneck hUn hfront L).map x w) =
      g.inner (L.map x) (mfderiv (𝓡 3) (𝓡 3) L.map x v)
        (mfderiv (𝓡 3) (𝓡 3) L.map x w) := by
  have hxΩ := referenceRetained_subset U L hx
  have hxC : L.map x ∈ closure (U : Set S.carrier) :=
    (referenceRetained_image U L).subset (mem_image_of_mem _ hx)
  have hdL := ((L.map_smooth x hxΩ).contMDiffAt (hΩ.mem_nhds hxΩ)).mdifferentiableAt (by simp)
  have hdr := (retainedMap_localDiffeomorphAt I R U hU hd hc hneck hUn (L.map x)
    (closure_retained_subset_neighborhood I U hfront hxC)).mdifferentiableAt (by simp)
  change (cutMetric I R U hU hd hc).inner (retainedMap I R U hU hd hc (L.map x))
    (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc ∘ L.map) x v)
    (mfderiv (𝓡 3) (𝓡 3) (retainedMap I R U hU hd hc ∘ L.map) x w) = _
  rw [mfderiv_comp_apply x hdr hdL v, mfderiv_comp_apply x hdr hdL w]
  exact retainedMap_metric I R U hU hd hc hneck hUn hfront (L.map x) hxC _ _

end PoincareConjecture.Surgery.Terminal.Gluing

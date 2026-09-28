import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinarySlices

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}

def ordinaryChapter11Source (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] :
    GeneralizedSliceCarrier where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

noncomputable def ordinaryChapter11Box (R : OrdinaryProductSpacetimeConclusion F.metric I) :
    GeneralizedRicciFlowBox (ordinaryChapter11Slice R)
      (fun t => (R.slices t).metricOnPoints) I.domain where
  carrier := ordinaryChapter11Source M
  interval := I.domain
  relatively_open := ⟨univ, isOpen_univ, (inter_univ _).symm⟩
  flow := F
  forward := fun t ht => R.sliceIdentification ⟨t, ht⟩
  inverse := fun t ht => (R.sliceIdentification ⟨t, ht⟩).symm
  forward_openEmbedding := fun t ht => (R.sliceIdentification ⟨t, ht⟩).toHomeomorph.isOpenEmbedding
  forward_smooth := fun t ht => (R.sliceIdentification ⟨t, ht⟩).contMDiff
  inverse_smooth := fun t ht => (R.sliceIdentification ⟨t, ht⟩).symm.contMDiff.contMDiffOn
  left_inverse := fun t ht => (R.sliceIdentification ⟨t, ht⟩).left_inv
  right_inverse := fun t ht x _ => (R.sliceIdentification ⟨t, ht⟩).right_inv x
  metric_pullback := fun t ht => R.sliceMetric_eq ⟨t, ht⟩

set_option backward.isDefEq.respectTransparency false in

noncomputable def ordinaryChapter11Flow (R : OrdinaryProductRicciGeometry F.metric I) :
    GeneralizedRicciFlowData where
  slice := ordinaryChapter11Slice R.product
  interval := I.domain
  interval_connected := I.ordConnected
  interval_nontrivial := I.nontrivial
  slice_nonempty_iff := ordinaryChapter11Slice_nonempty R.product
  metric := fun t => (R.product.slices t).metricOnPoints
  connection := R.leafwiseConnection.sliceConnection
  space_topology := ordinaryChapter11Topology R.product
  space_t2 := by
    let := ordinaryChapter11Topology R.product
    let : T2Space R.product.spacetime.Point := R.product.spacetime.t2Space
    exact (ordinaryChapter11Homeomorph R.product).isEmbedding.t2Space
  space_secondCountable := by
    let := ordinaryChapter11Topology R.product
    let : SecondCountableTopology R.product.spacetime.Point :=
      R.product.spacetime.secondCountable
    exact (ordinaryChapter11Homeomorph R.product).isEmbedding.secondCountableTopology
  time_continuous := by
    let := ordinaryChapter11Topology R.product
    have hc : Continuous R.product.spacetime.timeFunction :=
      continuous_subtype_val.comp continuous_fst
    have h := hc.comp
      (ordinaryChapter11Homeomorph R.product).continuous
    exact h.congr (fun z => z.2.property)
  slice_embedding := by
    let := ordinaryChapter11Topology R.product
    intro t
    apply (ordinaryChapter11Homeomorph R.product).isEmbedding.of_comp_iff.mp
    exact (R.product.slices t).inclusion_embedding
  box_index := ULift.{u} Unit
  box := fun _ => ordinaryChapter11Box (F := F) R.product
  box_openEmbedding := by
    let := ordinaryChapter11Topology R.product
    intro _
    have he : (fun p : I.domain × M =>
        (⟨p.1.val, R.product.sliceIdentification p.1 p.2⟩ :
          Σ t : ℝ, (ordinaryChapter11Slice R.product t).carrier)) =
        (ordinaryChapter11Homeomorph R.product).symm := by
      funext p
      apply (ordinaryChapter11Flatten R.product).injective
      exact R.product.sliceIdentification_eq p.1 p.2
    change Topology.IsOpenEmbedding
      (fun p : I.domain × M => (⟨p.1.val, R.product.sliceIdentification p.1 p.2⟩ :
        Σ t : ℝ, (ordinaryChapter11Slice R.product t).carrier))
    rw [he]
    exact (ordinaryChapter11Homeomorph R.product).symm.isOpenEmbedding
  box_covers := by
    intro t x
    have ht : t ∈ I.domain := (ordinaryChapter11Slice_nonempty R.product t).mp ⟨x⟩
    exact ⟨⟨()⟩, ht, (R.product.sliceIdentification ⟨t, ht⟩).symm x,
      (R.product.sliceIdentification ⟨t, ht⟩).apply_symm_apply x⟩
  vertical_compatibility := by
    intro _ _ t ht hc x y hxy s hs hs'
    have h : x = y := (R.product.sliceIdentification ⟨t, ht⟩).injective hxy
    subst y
    rfl

end PoincareConjecture.M34

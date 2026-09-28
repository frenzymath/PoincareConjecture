import PoincareConjecture.Proofs.M12.GeneralizedTransitions
import PoincareConjecture.Statements.M11GeneralizedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable (F : GeneralizedRicciFlowData.{u})

noncomputable def refinedTransition (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval)
    (x : spatialChartDomain b.2) (y : spatialChartDomain c.2)
    (hxy : refinedSliceMap F b t hb x = refinedSliceMap F c t hc y) :
    AdaptedMetricTransition (refinedBox F b) (refinedBox F c) t x.val y.val where
  interval := commonInterval F b.1 c.1 t hb hc
  interval_relatively_open := by
    obtain ⟨U, hU, hUb⟩ := (F.box b.1).relatively_open
    obtain ⟨V, hV, hVc⟩ := (F.box c.1).relatively_open
    refine ⟨U ∩ V, hU.inter hV, ?_⟩
    change (F.box b.1).interval ∩ (F.box c.1).interval = F.interval ∩ (U ∩ V)
    rw [hUb, hVc]
    exact (inter_inter_distrib_left F.interval U V).symm
  interval_subset_left := inter_subset_left
  interval_subset_right := inter_subset_right
  time_mem := ⟨hb, hc⟩
  coordinateChange := coordinateTransition F b c t hb hc
  source_subset := fun _ hx => hx.1.1
  target_subset := fun _ hy => hy.1.1
  source_mem := by
    refine ⟨⟨x.property, mem_univ _⟩, ?_⟩
    change refinedSliceMap F b t hb x ∈ (refinedSliceMap F c t hc).target
    rw [hxy]
    exact (refinedSliceMap F c t hc).map_source ⟨y.property, mem_univ _⟩
  map_marked := by
    change (refinedSliceMap F c t hc).symm (refinedSliceMap F b t hb x) = y.val
    rw [hxy]
    exact (refinedSliceMap F c t hc).left_inv ⟨y.property, mem_univ _⟩
  smooth := coordinateTransition_smooth F b c t hb hc
  symm_smooth := coordinateTransition_inverse_smooth F b c t hb hc
  box_eq := by
    intro s hs z hz
    exact congrArg (fun a : (F.slice s).carrier => (⟨s, a⟩ : F.point))
      (coordinateTransition_worldline F b c t hb hc s hs.1 hs.2 z hz)
  metric_eq := fun s hs z hz v w =>
    coordinateTransition_metric F b c t hb hc s hs.1 hs.2 z hz v w

noncomputable def flowBoxAtlas : AdaptedMetricAtlas 3 F.point where
  time := Sigma.fst
  interval := flowInterval F
  time_continuous := F.time_continuous
  time_range := by
    ext t
    constructor
    · rintro ⟨p, rfl⟩
      exact (F.slice_nonempty_iff p.1).mp ⟨p.2⟩
    · intro ht
      obtain ⟨x⟩ := (F.slice_nonempty_iff t).mpr ht
      exact ⟨⟨t, x⟩, rfl⟩
  box_index := refinedBoxIndex F
  box := refinedBox F
  box_covers := by
    rintro ⟨t, x⟩
    obtain ⟨b, ht, y, hy⟩ := F.box_covers t x
    refine ⟨⟨b, y⟩, (⟨t, ht⟩, ⟨chartAt (EuclideanSpace ℝ (Fin 3)) y y,
      mem_chart_target _ y⟩), ?_⟩
    change (⟨t, (F.box b).forward t ht
      ((chartAt (EuclideanSpace ℝ (Fin 3)) y).symm
        (chartAt (EuclideanSpace ℝ (Fin 3)) y y))⟩ : F.point) = ⟨t, x⟩
    rw [(chartAt (EuclideanSpace ℝ (Fin 3)) y).left_inv (mem_chart_source _ y), hy]
  transitions := by
    intro b c t hb hc x y hxy
    refine ⟨refinedTransition F b c t hb hc x y ?_⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2

def flowSliceLabel (t : ℝ) : SpacetimeSliceLabel 3 F.point Sigma.fst t where
  carrier := (F.slice t).carrier
  topologicalSpace := (F.slice t).topologicalSpace
  chartedSpace := (F.slice t).chartedSpace
  isManifold := (F.slice t).isManifold
  measurableSpace := (F.slice t).measurableSpace
  borelSpace := (F.slice t).borelSpace
  metric := F.metric t
  toSpacetime x := ⟨t, x⟩
  embedding := F.slice_embedding t
  time_eq _ := rfl
  range_eq := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · rcases p with ⟨s, x⟩
      intro h
      change s = t at h
      subst s
      exact ⟨x, rfl⟩

noncomputable def flowSliceLabeling : SpacetimeSliceLabeling (flowBoxAtlas F) where
  slice := flowSliceLabel F
  boxMap b t ht x := (F.box b.1).forward t ht (spatialChartInverse b.2 x)
  boxMap_smooth b t ht := ((F.box b.1).forward_smooth t ht).comp
    (spatialChartInverse_smooth b.2)
  boxMap_eq _ _ _ _ := rfl
  metric_eq := by
    intro b t ht x v w
    have hchart := (spatialChartInverse_smooth b.2 x).mdifferentiableAt (by simp)
    have hf := ((F.box b.1).forward_smooth t ht (spatialChartInverse b.2 x)).mdifferentiableAt
      (by simp)
    change (F.metric t).inner ((F.box b.1).forward t ht (spatialChartInverse b.2 x))
      (mfderiv (𝓡 3) (𝓡 3) ((F.box b.1).forward t ht ∘ spatialChartInverse b.2) x v)
      (mfderiv (𝓡 3) (𝓡 3) ((F.box b.1).forward t ht ∘ spatialChartInverse b.2) x w) = _
    rw [mfderiv_comp_apply x hf hchart v, mfderiv_comp_apply x hf hchart w,
      (F.box b.1).metric_pullback t ht (spatialChartInverse b.2 x),
      spatialChartInverse_mfderiv, spatialChartInverse_mfderiv]
    rfl

theorem flowBoxAtlas_realize (h : GeneralizedSpacetimeGeometryTheory.{u} 3) :
    Nonempty (GeneralizedFlowCarrierConclusion (flowBoxAtlas F)) := by
  let : T2Space F.point := F.space_t2
  let : SecondCountableTopology F.point := F.space_secondCountable
  exact h.realize F.point (flowBoxAtlas F)

theorem flowSlice_identification (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
    (t : ℝ) :
    Nonempty (SpacetimeSliceIdentification R.spacetime t (R.slices t) (flowSliceLabel F t)) :=
  R.supplied_labels (flowSliceLabeling F) t

end PoincareConjecture.Proofs.M12

import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.Spacetime.Realization.OrdinaryProduct.Atlas
import PoincareLib.Geometry.Spacetime.Realization.Interval.Topology

/-!
# Actual generalized flow boxes in manifold coordinates

Morgan--Tian Definitions 3.34-3.38, pp. 59-61. Refinement keeps the original
box interval, spatial map and ordinary metric. Empty carriers contribute no
refined boxes. No smooth spacetime structure is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpochExtension.Spacetime

open Poincare.Spacetime.Realization

variable (F : GeneralizedRicciFlowData.{u})

def flowInterval : SpacetimeInterval :=
  ⟨F.interval, F.interval_connected, F.interval_nontrivial⟩

def boxInterval (b : F.box_index) : SpacetimeInterval :=
  ⟨(F.box b).interval, (F.box b).flow.interval, (F.box b).flow.nontrivial⟩

/-- The actual inverse supplied by the box, restricted to its open image. -/
def boxSliceMap (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval) :
    OpenPartialHomeomorph (F.box b).carrier.carrier (F.slice t).carrier where
  toFun := (F.box b).forward t ht
  invFun := (F.box b).inverse t ht
  source := univ
  target := range ((F.box b).forward t ht)
  map_source' x _ := ⟨x, rfl⟩
  map_target' _ _ := mem_univ _
  left_inv' x _ := (F.box b).left_inverse t ht x
  right_inv' := (F.box b).right_inverse t ht
  open_source := isOpen_univ
  open_target := ((F.box b).forward_openEmbedding t ht).isOpen_range
  continuousOn_toFun := ((F.box b).forward_smooth t ht).continuous.continuousOn
  continuousOn_invFun := ((F.box b).inverse_smooth t ht).continuousOn

def refinedBoxIndex := Σ b : F.box_index, (F.box b).carrier.carrier

noncomputable def refinedBox (b : refinedBoxIndex F) :
    AdaptedMetricBox 3 F.point Sigma.fst (flowInterval F) where
  interval := boxInterval F b.1
  spatial := spatialChartDomain b.2
  spatial_nonempty := ⟨chartAt (EuclideanSpace ℝ (Fin 3)) b.2 b.2,
    mem_chart_target _ b.2⟩
  interval_relatively_open := (F.box b.1).relatively_open
  toSpacetime q := ⟨q.1.1, (F.box b.1).forward q.1.1 q.1.2 (spatialChartInverse b.2 q.2)⟩
  openEmbedding := (F.box_openEmbedding b.1).comp
    (Topology.IsOpenEmbedding.id.prodMap (spatialChartInverse_openEmbedding b.2))
  time_toSpacetime _ := rfl
  metric := ordinaryChartMetric (F.box b.1).flow.metric b.2
  metric_smooth := ordinaryChartMetric_smooth _ _ (F.box b.1).flow.smooth b.2
  metric_symm := fun t _ x _ v w => ordinaryChartMetric_symm _ b.2 t x v w
  metric_pos := fun t _ x hx v hv => ordinaryChartMetric_pos _ b.2 t x hx v hv

/-- Relative openness gives a nontrivial overlap even at a global endpoint. -/
theorem commonInterval_nontrivial (b c : F.box_index) (t : ℝ)
    (hb : t ∈ (F.box b).interval) (hc : t ∈ (F.box c).interval) :
    ((F.box b).interval ∩ (F.box c).interval).Nontrivial := by
  obtain ⟨U, hU, hUb⟩ := (F.box b).relatively_open
  obtain ⟨V, hV, hVc⟩ := (F.box c).relatively_open
  have htI : t ∈ F.interval := by rw [hUb] at hb; exact hb.1
  have htUV : t ∈ U ∩ V := by
    rw [hUb] at hb
    rw [hVc] at hc
    exact ⟨hb.2, hc.2⟩
  have hacc := ((interval_uniqueDiffOn (flowInterval F) t htI).inter
    ((hU.inter hV).mem_nhds htUV)).accPt
  obtain ⟨s, hs, hst⟩ := accPt_iff_nhds.mp hacc univ univ_mem
  refine ⟨s, ?_, t, ⟨hb, hc⟩, hst⟩
  rw [hUb, hVc]
  exact ⟨⟨hs.2.1, hs.2.2.1⟩, ⟨hs.2.1, hs.2.2.2⟩⟩

def commonInterval (b c : F.box_index) (t : ℝ)
    (hb : t ∈ (F.box b).interval) (hc : t ∈ (F.box c).interval) :
    SpacetimeInterval where
  domain := (F.box b).interval ∩ (F.box c).interval
  ordConnected := (F.box b).flow.interval.inter (F.box c).flow.interval
  nontrivial := commonInterval_nontrivial F b c t hb hc

end PoincareMT.EpochExtension.Spacetime

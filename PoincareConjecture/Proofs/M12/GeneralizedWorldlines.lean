import PoincareConjecture.Proofs.M12.GeneralizedCylinderClock
import PoincareConjecture.Proofs.M11.SelectedIntervalLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

theorem rawCylinderMap_local_box
    (t : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point)
    (x : U) :
    ∃ L : SpacetimeInterval,
      ∃ hK : L.domain ⊆ (cylinderPhysicalInterval a q e.scale_pos J).domain,
        t.val ∈ L.domain ∧
        IsOpen {v : (cylinderPhysicalInterval a q e.scale_pos J).domain | v.val ∈ L.domain} ∧
        ∃ b : F.box_index, ∃ hb : L.domain ⊆ (boxInterval F b).domain,
          ∃ y : (F.box b).carrier.carrier,
            ∀ v : (R.timeIntervals.interval L).Point,
              rawCylinderMap R e
                  (spacetimeIntervalInclusion (R.timeIntervals.interval L)
                    (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) hK v,
                    x) =
                originalBoxMap F R b
                  (spacetimeIntervalInclusion (R.timeIntervals.interval L)
                    (R.timeIntervals.interval (boxInterval F b)) hb v, y) := by
  let K := cylinderPhysicalInterval a q e.scale_pos J
  let c := cylinderClockHomeomorph a q e.scale_pos J
  obtain ⟨b, y, δ, hδ, hv⟩ :=
    e.vertical_compatibility (c t).val (c t).property x.val x.property
  let V : Set K.domain := {v | |(c v).val - (c t).val| < δ}
  have hV : V ∈ 𝓝 t := by
    have hc : Continuous (fun v : K.domain => |(c v).val - (c t).val|) := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds (by simpa using hδ)
  obtain ⟨L, hK, htL, ho, hLV⟩ := interval_exists_open_small_neighborhood K t hV
  have hbox : L.domain ⊆ (boxInterval F b).domain := by
    intro v hvL
    let w : K.domain := ⟨v, hK hvL⟩
    obtain ⟨hb, _⟩ := hv (c w).val (c w).property (hLV ⟨v, hvL⟩)
    change parabolicTimeInv q a (parabolicTime q a v) ∈ (F.box b).interval at hb
    change v ∈ (F.box b).interval
    simpa only [parabolicTimeInv_parabolicTime q e.scale_pos] using hb
  refine ⟨L, hK, htL, ho, b, hbox, y, ?_⟩
  intro v
  let w : K.domain := ⟨v.val, hK v.property⟩
  obtain ⟨hb, heq⟩ := hv (c w).val (c w).property (hLV v)
  have hp : e.pointMap (c w).val (c w).property x.val =
      (⟨a + (c w).val / q, (F.box b).forward (a + (c w).val / q) hb y⟩ : F.point) :=
    congrArg (fun z => (⟨a + (c w).val / q, z⟩ : F.point)) heq
  have ht : a + (c w).val / q = v.val :=
    parabolicTimeInv_parabolicTime q e.scale_pos a v.val
  change e.pointMap (c w).val (c w).property x.val =
    (⟨v.val, (F.box b).forward v.val (hbox v.property) y⟩ : F.point)
  exact hp.trans (congrArg
    (fun z : (boxInterval F b).domain =>
      (⟨z.val, (F.box b).forward z.val z.property y⟩ : F.point))
    (show (⟨a + (c w).val / q, hb⟩ : (boxInterval F b).domain) =
      ⟨v.val, hbox v.property⟩ from Subtype.ext ht))

theorem rawCylinderMap_worldline_smooth (x : U) :
    ContMDiff (𝓡∂ 1) (spacetimeModel 3) ∞
      (fun t => rawCylinderMap R e (t, x)) := by
  intro t
  obtain ⟨L, hK, htL, ho, b, hb, y, heq⟩ := rawCylinderMap_local_box R e t x
  let tL : (R.timeIntervals.interval L).Point := ⟨t.val, htL⟩
  have hf : ContMDiff (𝓡∂ 1) (spacetimeModel 3) ∞
      (fun v : (R.timeIntervals.interval L).Point => rawCylinderMap R e
        (spacetimeIntervalInclusion (R.timeIntervals.interval L)
          (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) hK v, x)) := by
    have hfun := funext heq
    rw [hfun]
    exact ((originalBoxCylinder F R b).worldline_smooth y).comp
      (R.timeIntervals.inclusion_smooth L (boxInterval F b) hb)
  exact selectedInterval_smoothAt_of_local R _ L hK ho tL
    (fun s => rawCylinderMap R e (s, x)) (hf tL)

theorem rawCylinderMap_worldline_derivative
    (t : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point)
    (x : U) :
    mfderiv (𝓡∂ 1) (spacetimeModel 3) (fun s => rawCylinderMap R e (s, x)) t
      ((R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).positiveTangent t) =
      R.spacetime.timeVector (rawCylinderMap R e (t, x)) := by
  obtain ⟨L, hK, htL, ho, b, hb, y, heq⟩ := rawCylinderMap_local_box R e t x
  let tL : (R.timeIntervals.interval L).Point := ⟨t.val, htL⟩
  let j := spacetimeIntervalInclusion (R.timeIntervals.interval L)
    (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) hK
  let k := spacetimeIntervalInclusion (R.timeIntervals.interval L)
    (R.timeIntervals.interval (boxInterval F b)) hb
  let f := fun s => rawCylinderMap R e (s, x)
  let g := fun s => originalBoxMap F R b (s, y)
  have hj : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) j tL :=
    (R.timeIntervals.inclusion_smooth L _ hK tL).mdifferentiableAt (by simp)
  have hk : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) k tL :=
    (R.timeIntervals.inclusion_smooth L _ hb tL).mdifferentiableAt (by simp)
  have hf := (rawCylinderMap_worldline_smooth R e x (j tL)).mdifferentiableAt (by simp)
  have hg := ((originalBoxCylinder F R b).worldline_smooth y (k tL)).mdifferentiableAt
    (by simp)
  have hleft := mfderiv_comp_apply tL hf hj ((R.timeIntervals.interval L).positiveTangent tL)
  have hright := mfderiv_comp_apply tL hg hk ((R.timeIntervals.interval L).positiveTangent tL)
  have hfun : f ∘ j = g ∘ k := funext heq
  change mfderiv (𝓡∂ 1) (spacetimeModel 3) (f ∘ j) tL _ = _ at hleft
  rw [R.timeIntervals.inclusion_derivative] at hleft hright
  have hdiff := congrArg
    (fun l : (R.timeIntervals.interval L).Point → R.spacetime.Point =>
      (mfderiv (𝓡∂ 1) (spacetimeModel 3) l tL
        ((R.timeIntervals.interval L).positiveTangent tL) :
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))) hfun
  have hpoint : g (k tL) = f t := (heq tL).symm
  exact hleft.symm.trans (hdiff.trans (hright.trans
    (((originalBoxCylinder F R b).worldline_derivative (k tL) y).trans
      (congrArg (fun p => (R.spacetime.timeVector p :
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))) hpoint))))

noncomputable def rawCylinderWorldline
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval) (x : U) :
    SpacetimeWorldline R.spacetime
      (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) where
  interval_subset := hI
  curve t := rawCylinderMap R e (t, x)
  smooth := rawCylinderMap_worldline_smooth R e x
  time_eq t := rawCylinderMap_time R e (t, x)
  derivative_eq t := rawCylinderMap_worldline_derivative R e t x

end PoincareConjecture.Proofs.M12

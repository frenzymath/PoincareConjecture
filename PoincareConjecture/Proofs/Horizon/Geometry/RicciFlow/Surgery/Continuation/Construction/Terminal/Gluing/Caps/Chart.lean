import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.CapChart







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def capChart (i : ι) : SurgeryCapChart g₀ (cutCarrier I R U hU hd hc)
    (cutMetric I R U hU hd hc) (I i).neck.scale := by
  let e := capEmbedding I R U hU hd hc i
  let D := {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)}
  let C := closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))
  have hD : D = Metric.closedBall 0 (R i).capEuclideanRadius :=
    MetricSurgery.standard_closed_ball_eq_euclidean g₀
      (by linarith [g₀.cylindrical_end.radius_pos])
  have hD₅ : D ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) := by
    rw [hD]
    exact (R i).capEuclidean_closedBall_subset
  have hC : (R i).cap_map '' D = C := (R i).cap_closed_image
  have hC₅ : C ⊆ (R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) := by
    rw [← hC]
    exact image_mono hD₅
  have hinv : MapsTo e.symm (e '' C) C := by
    rintro y ⟨x, hx, rfl⟩
    rwa [e.left_inv (mem_univ x)]
  let H : D ≃ₜ e '' C :=
    ((Homeomorph.setCongr hD).trans (R i).closedCapHomeomorph).trans
      ((capInclusion_openEmbedding I R U hU hd hc i).isEmbedding.homeomorphImage C)
  refine
    { radius := g₀.cylindrical_end.radius + 4
      radius_eq := rfl
      tip := e (R i).tip
      map := e ∘ (R i).cap_map
      inverse := (R i).cap_inverse ∘ e.symm
      domain := D
      domain_eq := rfl
      carrier := e '' C
      image := by rw [image_comp, hC]
      carrier_compact := (R i).isCompact_closed_cap.image
        (capInclusion_openEmbedding I R U hU hd hc i).continuous
      homeomorph := H
      homeomorph_eq := fun _ => rfl
      map_tip := congrArg e (R i).cap_map_tip
      left_inverse := ?_
      right_inverse := ?_
      map_smooth := ?_
      inverse_smooth := ?_
      inner_ball := ?_
      outer_ball := capInclusion_closed_outer_ball I R U hU hd hc i }
  · intro x hx
    change (R i).cap_inverse (e.symm (e ((R i).cap_map x))) = x
    rw [e.left_inv (mem_univ _)]
    exact (R i).cap_left_inverse (hD₅ hx)
  · rintro y ⟨x, hx, rfl⟩
    change e ((R i).cap_map ((R i).cap_inverse (e.symm (e x)))) = e x
    rw [e.left_inv (mem_univ x), (R i).cap_right_inverse (hC₅ hx)]
  · exact (capInclusion_localDiffeomorph I R U hU hd hc i).contMDiff.comp_contMDiffOn
      ((R i).cap_map_smooth.mono hD₅)
  · apply (R i).cap_inverse_smooth.comp
      ((capEmbedding_symm_smooth I R U hU hd hc i).mono ?_)
      (fun y hy => hC₅ (hinv hy))
    rintro y ⟨x, _, rfl⟩
    exact e.map_source (mem_univ x)
  · exact (capInclusion_inner_ball I R U hU hd hc i).trans (image_mono subset_closure)

@[simp] theorem capChart_tip (i : ι) :
    (capChart I R U hU hd hc i).tip = capInclusion I R U hU hd hc i (R i).tip := rfl

@[simp] theorem capChart_map (i : ι) (x : StandardCapSpace) :
    (capChart I R U hU hd hc i).map x =
      capInclusion I R U hU hd hc i ((R i).cap_map x) := rfl

@[simp] theorem capChart_carrier (i : ι) :
    (capChart I R U hU hd hc i).carrier =
      capInclusion I R U hU hd hc i ''
        closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := rfl

theorem capChart_disjoint : Pairwise (fun i j =>
    Disjoint (capChart I R U hU hd hc i).carrier (capChart I R U hU hd hc j).carrier) := by
  intro i j hij
  exact (capInclusion_disjoint I R U hU hd hc hij).mono
    (image_subset_range _ _) (image_subset_range _ _)

end PoincareConjecture.Surgery.Terminal.Gluing

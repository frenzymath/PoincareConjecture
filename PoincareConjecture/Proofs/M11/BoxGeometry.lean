import PoincareConjecture.Proofs.M11.BoxTransitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem adapted_time_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ A.time := by
  let := adaptedChartedSpace A
  intro p
  let b := Classical.choose (box_targets_cover A p)
  let := intervalChartedSpace (A.box b).interval
  have hp : p ∈ (boxHomeomorph (A.box b)).target :=
    Classical.choose_spec (box_targets_cover A p)
  have hinverse := cover_inverse_smooth (fun b ↦ boxHomeomorph (A.box b))
    (box_targets_cover A) (box_transition_smooth A) b
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q : boxDomain (A.box b) ↦ q.1.val) :=
    (smoothInterval (A.box b).interval).inclusion_smooth.comp contMDiff_fst
  have hcomp := htime.contMDiffAt.comp p
    (hinverse.contMDiffAt ((boxHomeomorph (A.box b)).open_target.mem_nhds hp))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(boxHomeomorph (A.box b)).open_target.mem_nhds hp] with q hq
  exact (boxHomeomorph_inverse_time (A.box b) hq).symm

theorem adapted_boundary_eq (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    (spacetimeModel n).boundary X = {p | A.time p ∈ frontier A.interval.domain} := by
  let := adaptedChartedSpace A
  ext p
  let b := Classical.choose (box_targets_cover A p)
  let q := (boxHomeomorph (A.box b)).symm p
  have hp : p ∈ (boxHomeomorph (A.box b)).target :=
    Classical.choose_spec (box_targets_cover A p)
  change (q ∈ (spacetimeModel n).boundary (boxDomain (A.box b))) ↔
    A.time p ∈ frontier A.interval.domain
  rw [ModelWithCorners.boundary_of_boundaryless_right,
    (smoothInterval (A.box b).interval).boundary_eq]
  change (q.1.val ∈ frontier (A.box b).interval.domain ∧ q.2 ∈ univ) ↔
    A.time p ∈ frontier A.interval.domain
  rw [and_iff_left (mem_univ _),
    interval_frontier_of_relatively_open A.interval (A.box b).interval
      (A.box b).interval_relatively_open q.1.property,
    boxHomeomorph_inverse_time (A.box b) hp]

theorem adapted_t3Space [hX : T2Space X] (A : AdaptedMetricAtlas n X) : T3Space X := by
  let := adaptedChartedSpace A
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := by
    change LocallyCompactSpace {x : EuclideanSpace ℝ (Fin 1) // 0 ≤ x 0}
    have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin 1) | 0 ≤ x 0} :=
      isClosed_le continuous_const (by fun_prop)
    exact hclosed.locallyCompactSpace
  let : LocallyCompactSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) := by
    change LocallyCompactSpace (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin n))
    infer_instance
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace
      (H := ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
      (M := X)
  have hregular : RegularSpace X :=
    RegularSpace.of_hasBasis (fun x : X ↦ compact_basis_nhds x)
      (fun _ _ h ↦ h.2.isClosed)
  exact {
    toT0Space := @T1Space.t0Space X _ (@T2Space.t1Space X _ hX)
    toRegularSpace := hregular
  }

end PoincareConjecture.Proofs.M11

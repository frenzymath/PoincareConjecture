import PoincareConjecture.Proofs.M38.StandardCapBall
import PoincareConjecture.Proofs.M38.SmoothChart
import PoincareConjecture.Proofs.M38.NeckCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem neck_region_open (N : EpsilonNeck g) (a b : ℝ) : IsOpen (N.region a b) := by
  have heq : N.region a b = N.carrier ∩
      N.coordinate_inverse ⁻¹' (Set.univ ×ˢ Set.Ioo a b) := by
    ext x
    simp [EpsilonNeck.region, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact N.coordinate_inverse_smooth.continuousOn.isOpen_inter_preimage
    N.carrier_open (isOpen_univ.prod isOpen_Ioo)

theorem neck_central_extended (N : EpsilonNeck g) :
    N.central_sphere ⊆ N.region (-N.epsilon⁻¹) 1 := by
  intro x hx
  have hcarrier := N.central_sphere_subset hx
  rw [N.central_sphere_eq] at hx
  obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hx
  have hs0 : s = 0 := hs
  subst s
  have hdomain : (z, (0 : ℝ)) ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    neck_central_domain N ⟨Set.mem_univ z, Set.mem_singleton (0 : ℝ)⟩
  refine ⟨hcarrier, ?_, ?_⟩ <;> rw [neck_coordinate_inverse_map N hdomain]
  · exact neg_neg_of_pos (inv_pos.mpr N.epsilon_pos)
  · exact zero_lt_one

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)

theorem local_collapse_collar_open :
    IsOpen (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) :=
  smooth_left_inverse_image_open (neck_region_open I.neck _ _)
    R.retained_smooth R.retained_inverse_smooth R.retained_left_inverse
    (neck_region_open I.neck _ _) Set.Subset.rfl

theorem local_collapse_inverse_mem {y : R.output.carrier}
    (hy : y ∈ R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) :
    R.retained_inverse y ∈ I.neck.region (-I.neck.epsilon⁻¹) 1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [R.retained_left_inverse hx]

theorem local_cap_image_open {U : Set StandardCapSpace} (hU : IsOpen U)
    (hsub : U ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    IsOpen (R.cap_map '' U) :=
  smooth_left_inverse_image_open (standard_ball_open _ _) R.cap_map_smooth
    R.cap_inverse_smooth R.cap_left_inverse hU hsub

theorem local_cap_closure_image {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    closure (R.cap_map '' Metric.ball 0 r) = R.cap_map '' Metric.closedBall 0 r := by
  have hc : ContinuousOn R.cap_map (closure (Metric.ball (0 : StandardCapSpace) r)) := by
    rw [closure_ball _ hr.ne']
    exact R.cap_map_smooth.continuousOn.mono hsub
  apply (closure_minimal (Set.image_mono Metric.ball_subset_closedBall)
    ((isCompact_closedBall (0 : StandardCapSpace) r).image_of_continuousOn
      (R.cap_map_smooth.continuousOn.mono hsub)).isClosed).antisymm
  simpa only [closure_ball _ hr.ne'] using hc.image_closure

theorem local_cap_frontier_image {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    frontier (R.cap_map '' Metric.ball 0 r) = R.cap_map '' Metric.sphere 0 r := by
  rw [(local_cap_image_open R Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hsub)).frontier_eq,
    local_cap_closure_image R hr hsub]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hout⟩
    refine ⟨x, ?_, rfl⟩
    have hn : x ∉ Metric.ball (0 : StandardCapSpace) r := fun h =>
      hout (Set.mem_image_of_mem R.cap_map h)
    exact le_antisymm hx (le_of_not_gt hn)
  · rintro ⟨x, hx, rfl⟩
    have hxclosed : x ∈ Metric.closedBall (0 : StandardCapSpace) r := hx.le
    refine ⟨Set.mem_image_of_mem R.cap_map hxclosed, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzx := R.cap_left_inverse.injOn (hsub (Metric.ball_subset_closedBall hz))
      (hsub hxclosed) heq
    subst z
    exact (ne_of_lt hz) hx

theorem local_cap_sphere_eq_collapse {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (hsub : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    R.cap_map '' Metric.sphere 0 r = R.collapse '' I.neck.central_sphere := by
  rw [R.cap_boundary, hball, local_cap_frontier_image R hr hsub]

theorem local_cap_boundary_neighborhood {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (hsub : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    IsOpen (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∩
      R.cap_map ⁻¹' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1)) ∧
    Metric.sphere 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∩
      R.cap_map ⁻¹' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) := by
  refine ⟨R.cap_map_smooth.continuousOn.isOpen_inter_preimage
    (standard_ball_open _ _) (local_collapse_collar_open R), ?_⟩
  intro x hx
  refine ⟨hsub hx.le, ?_⟩
  apply Set.image_mono (neck_central_extended I.neck)
  rw [← local_cap_sphere_eq_collapse R hr hball hsub]
  exact Set.mem_image_of_mem R.cap_map hx

theorem local_cap_exterior_inverse {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (hsub : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
    {x : StandardCapSpace} (hx : x ∈ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
    (hout : x ∉ Metric.closedBall (0 : StandardCapSpace) r) :
    R.retained_inverse (R.cap_map x) ∈ I.neck.region (-I.neck.epsilon⁻¹) 0 ∧
      R.collapse (R.retained_inverse (R.cap_map x)) = R.cap_map x := by
  have hy : R.cap_map x ∈ (closure (R.cap_map ''
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ := by
    rw [hball, local_cap_closure_image R hr hsub]
    rintro ⟨z, hz, heq⟩
    exact hout ((R.cap_left_inverse.injOn (hsub hz) hx heq) ▸ hz)
  rw [R.cap_exterior] at hy
  obtain ⟨q, hq, heq⟩ := hy
  have hqext : q ∈ I.neck.region (-I.neck.epsilon⁻¹) 1 :=
    ⟨hq.1, hq.2.1, hq.2.2.trans zero_lt_one⟩
  have hinv : R.retained_inverse (R.cap_map x) = q := by
    rw [← heq, R.retained_left_inverse hqext]
  exact ⟨hinv ▸ hq, by rw [hinv]; exact heq⟩

end PoincareConjecture.M38

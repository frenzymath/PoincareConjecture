import PoincareConjecture.Proofs.M38.CapCollarGluing










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38


theorem capShell_central {r : ℝ} (hr : 0 < r) (c : ℝ) :
    capShellMap r c '' (Set.univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 r := by
  ext x
  constructor
  · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    simp [capShellMap, hs0, norm_smul, abs_of_pos hr]
  · intro hx
    have hnorm : ‖x‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    refine ⟨(capUnitDirection x, 0), ⟨Set.mem_univ _, Set.mem_singleton _⟩, ?_⟩
    simpa [capShellMap, hnorm] using capUnitDirection_radial x

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem neck_mem_central_of_coordinate_zero (N : EpsilonNeck g) {x : M}
    (hx : x ∈ N.carrier) (hzero : (N.coordinate_inverse x).2 = 0) :
    x ∈ N.central_sphere := by
  rw [N.central_sphere_eq]
  exact ⟨N.coordinate_inverse x, ⟨Set.mem_univ _, hzero⟩,
    neck_coordinate_map_inverse N hx⟩

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)


theorem local_cap_collar_central {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    localCapCollar R r c '' (Set.univ ×ˢ ({0} : Set ℝ)) = I.neck.central_sphere := by
  change (R.retained_inverse ∘ R.cap_map ∘ capShellMap r c) '' _ = _
  rw [Set.image_comp, Set.image_comp, capShell_central hr c,
    local_cap_sphere_eq_collapse R hr hball (standard_cap_ball_extended _ hr hball)]
  exact R.retained_left_inverse.image_image' (neck_central_extended I.neck)



theorem local_cap_interior_inverse_positive {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    {y : R.output.carrier}
    (hy : y ∈ R.cap_map '' Metric.ball 0 r)
    (hcollar : y ∈ R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) :
    R.retained_inverse y ∈ I.neck.region 0 I.neck.epsilon⁻¹ := by
  have hq := local_collapse_inverse_mem R hcollar
  have hmap : R.collapse (R.retained_inverse y) = y := by
    apply R.retained_right_inverse
    obtain ⟨q, _, hq⟩ := hcollar
    exact ⟨q, hq⟩
  have hinside : y ∈ R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) := by
    rwa [hball]
  have hnneg : ¬ (I.neck.coordinate_inverse (R.retained_inverse y)).2 < 0 := by
    intro hneg
    have hout : y ∈ (closure (R.cap_map ''
        g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ := by
      rw [R.cap_exterior]
      exact ⟨R.retained_inverse y, ⟨hq.1, hq.2.1, hneg⟩, hmap⟩
    exact hout (subset_closure hinside)
  have hnzero : (I.neck.coordinate_inverse (R.retained_inverse y)).2 ≠ 0 := by
    intro hzero
    have hcentral := neck_mem_central_of_coordinate_zero I.neck hq.1 hzero
    have hfront : y ∈ frontier (R.cap_map '' Metric.ball 0 r) := by
      rw [← hball, ← R.cap_boundary]
      exact ⟨R.retained_inverse y, hcentral, hmap⟩
    have hopen := local_cap_image_open R Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans (standard_cap_ball_extended _ hr hball))
    rw [hopen.frontier_eq] at hfront
    exact hfront.2 hy
  exact ⟨hq.1, lt_of_le_of_ne (le_of_not_gt hnneg) (Ne.symm hnzero),
    (I.neck.coordinate_inverse_mem _ hq.1).2.2⟩


theorem local_cap_collar_positive {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (hdom : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∩
        R.cap_map ⁻¹' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1))
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    {z : UnitTwoSphere} {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    localCapCollar R r c (z, s) ∈ I.neck.region 0 I.neck.epsilon⁻¹ := by
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Set.mem_univ _, neg_one_lt_zero.trans hs.1, hs.2⟩
  apply local_cap_interior_inverse_positive R (hc.trans hcr) hball ?_
    (hdom (capShell_mem hc hcr hz)).2
  refine Set.mem_image_of_mem R.cap_map ?_
  rw [Metric.mem_ball, dist_zero_right, capShell_norm hc hcr hz]
  have hcs : 0 < c * s := mul_pos hc hs.1
  linarith

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)


theorem event_cap_collar_central {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    eventCapCollar F T hT i r c '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      (F.event T hT).limit_identify.inverse '' ((F.event T hT).necks i).neck.central_sphere := by
  change ((F.event T hT).limit_identify.inverse ∘ localCapCollar _ r c) '' _ = _
  rw [Set.image_comp, local_cap_collar_central _ hr c hball]


theorem event_cap_collar_positive_discarded {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (hdom : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5) ∩
        ((F.event T hT).local_result i).cap_map ⁻¹'
          (((F.event T hT).local_result i).collapse ''
            ((F.event T hT).necks i).neck.region
              (-((F.event T hT).necks i).neck.epsilon⁻¹) 1))
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    Disjoint (eventCapCollar F T hT i r c '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1))
      (F.event T hT).retained_pre := by
  apply Set.disjoint_left.mpr
  rintro x ⟨⟨z, s⟩, hs, rfl⟩ hx
  have hpos := local_cap_collar_positive ((F.event T hT).local_result i)
    hc hcr hdom hball (z := z) hs.2
  apply Set.disjoint_left.mp ((F.event T hT).neck_positive_discarded i) hpos
  exact ⟨eventCapCollar F T hT i r c (z, s), hx,
    (F.event T hT).limit_identify.right_inverse (Set.mem_univ _)⟩

end PoincareConjecture.M38

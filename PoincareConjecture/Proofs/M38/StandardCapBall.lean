import PoincareConjecture.Proofs.M38.RotationMetric
import PoincareConjecture.Proofs.M38.RadialRegions
import PoincareConjecture.Proofs.M38.CapCorrespondence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

theorem cap_chart_domain_compact {g₀ : StandardInitialMetric}
    {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier} {h : ℝ}
    (C : SurgeryCapChart g₀ S g h) : IsCompact C.domain := by
  let : CompactSpace C.carrier := isCompact_iff_compactSpace.mp C.carrier_compact
  let : CompactSpace C.domain := C.homeomorph.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem riemannian_edist_continuous {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] (g : RiemannianMetric n M) :
    Continuous (fun p : M × M => g.edist p.1 p.2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change Continuous (fun p : M × M => EDist.edist p.1 p.2)
  exact continuous_edist

theorem standard_ball_open (g₀ : StandardInitialMetric) (r : ℝ) :
    IsOpen (g₀.metric.ball 0 r) :=
  isOpen_lt ((riemannian_edist_continuous g₀.metric).comp
    (continuous_const.prodMk continuous_id)) continuous_const

theorem standard_closed_ball_closed (g₀ : StandardInitialMetric) (r : ℝ) :
    IsClosed {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} :=
  isClosed_le ((riemannian_edist_continuous g₀.metric).comp
    (continuous_const.prodMk continuous_id)) continuous_const

theorem standard_cap_ball_eq_euclidean {g₀ : StandardInitialMetric}
    {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier} {h : ℝ}
    (C : SurgeryCapChart g₀ S g h) :
    ∃ r : ℝ, 0 < r ∧
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r := by
  have hr : 0 < g₀.cylindrical_end.radius + 4 := by
    linarith [g₀.cylindrical_end.radius_pos]
  have hcompact := cap_chart_domain_compact C
  rw [C.domain_eq, C.radius_eq] at hcompact
  apply radial_open_region_eq_ball (standard_ball_open _ _)
    (isPathConnected_ball _ _ hr).isConnected
  · let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g₀.metric.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) 0 0 < _
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  · apply hcompact.isBounded.subset
    intro x hx
    exact (show g₀.metric.edist 0 x <
      ENNReal.ofReal (g₀.cylindrical_end.radius + 4) from hx).le
  · exact standard_ball_radial g₀ _

theorem event_cap_euclidean_radius (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (i : Fin (F.event T hT).cap_count) :
    ∃ r : ℝ, 0 < r ∧
      F.standard_initial.metric.ball 0
        (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r ∧
      (F.event T hT).local_embed i ''
        (((F.event T hT).local_result i).cap_map '' Metric.closedBall 0 r) =
          ((F.event T hT).caps i).carrier := by
  obtain ⟨r, hr, hball⟩ := standard_cap_ball_eq_euclidean ((F.event T hT).caps i)
  let b := F.standard_initial.metric.ball 0
    (F.standard_initial.cylindrical_end.radius + 4)
  have hclosure : closure b ⊆ {x | F.standard_initial.metric.edist 0 x ≤
      ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 4)} := by
    apply closure_minimal ?_ (standard_closed_ball_closed _ _)
    intro x hx
    exact (show F.standard_initial.metric.edist 0 x <
      ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 4) from hx).le
  have hsub : closure b ⊆ F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 5) := by
    intro x hx
    exact (hclosure hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
      linarith [F.standard_initial.cylindrical_end.radius_pos])).mpr (by linarith))
  have hcompact : IsCompact (closure b) := by
    change IsCompact (closure (F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4)))
    rw [hball, closure_ball _ hr.ne']
    exact isCompact_closedBall _ _
  have hcont := ((F.event T hT).local_result i).cap_map_smooth.continuousOn.mono hsub
  have himage : closure (((F.event T hT).local_result i).cap_map '' b) =
      ((F.event T hT).local_result i).cap_map '' closure b :=
    (closure_minimal (Set.image_mono subset_closure)
      (hcompact.image_of_continuousOn hcont).isClosed).antisymm hcont.image_closure
  refine ⟨r, hr, hball, ?_⟩
  rw [← (F.event T hT).local_cap_image i]
  change _ = (F.event T hT).local_embed i ''
    closure (((F.event T hT).local_result i).cap_map '' b)
  rw [himage]
  change _ = (F.event T hT).local_embed i ''
    (((F.event T hT).local_result i).cap_map '' closure
      (F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 4)))
  rw [hball, closure_ball _ hr.ne']

end PoincareConjecture.M38

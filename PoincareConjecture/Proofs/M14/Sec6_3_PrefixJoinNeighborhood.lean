import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinGauge

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}

theorem prefixJoinGauge_nonempty (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (hc : c < τ₂) :
    Nonempty (PrefixJoinGauge q p) := by
  obtain ⟨b, N, lift, hN, hqN, hlift, hrec, htime⟩ := exists_smooth_gauge_lift G (q.curve c)
  let z := (lift (q.curve c)).2.val
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((G.gaugeCover.spatial b).isOpen.mem_nhds (lift (q.curve c)).2.property)
  let K := closedBall z (ε / 2)
  have hKsub : K ⊆ G.gaugeCover.spatial b :=
    (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  let V := N ∩ (fun w => (lift w).2.val) ⁻¹' ball z (ε / 2)
  have hcoords : ContinuousOn (fun w => (lift w).2.val) N :=
    continuous_subtype_val.comp_continuousOn hlift.continuousOn.snd
  have hV : IsOpen V := hcoords.isOpen_inter_preimage hN isOpen_ball
  have hqV : q.curve c ∈ V := ⟨hqN, mem_ball_self (by linarith)⟩
  have hpV : p.curve c ∈ V := by rw [p.curve_end]; exact hqV
  have hpnear := (p.curve_continuous c ⟨p.tau_lt.le, le_rfl⟩).preimage_mem_nhdsWithin
    (hV.mem_nhds hpV)
  obtain ⟨P, hP, hcP, hPV⟩ := mem_nhdsWithin.mp hpnear
  have hqnear : q.curve ⁻¹' V ∈ 𝓝 c :=
    (q.curve_continuous.continuousAt (Icc_mem_nhds p.tau_lt hc)).preimage_mem_nhds
      (hV.mem_nhds hqV)
  have hnear : P ∩ q.curve ⁻¹' V ∩ Ioo τ₁ τ₂ ∈ 𝓝 c :=
    inter_mem (inter_mem (hP.mem_nhds hcP) hqnear) (Ioo_mem_nhds p.tau_lt hc)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r := δ / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  have hwindow : Icc (c - r) (c + r) ⊆ P ∩ q.curve ⁻¹' V ∩ Ioo τ₁ τ₂ := by
    intro s hs
    apply hδsub
    change dist s c < δ
    rw [Real.dist_eq, abs_lt]
    dsimp only [r] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hprefix : ∀ s ∈ Icc (c - r) c, p.curve s ∈ V := by
    intro s hs
    have hw := hwindow (show s ∈ Icc (c - r) (c + r) from ⟨hs.1, by linarith [hs.2]⟩)
    exact hPV ⟨hw.1.1, hw.2.1.le, hs.2⟩
  refine ⟨{
    index := b
    image := V
    image_open := hV
    lift := lift
    lift_smooth := hlift.mono inter_subset_left
    lift_right := fun w hw => hrec w hw.1
    lift_time := fun w hw => htime w hw.1
    radius := r
    radius_pos := hr
    left_margin := (hwindow (show c - r ∈ Icc (c - r) (c + r) from
      ⟨le_rfl, by linarith⟩)).2.1
    right_margin := (hwindow (show c + r ∈ Icc (c - r) (c + r) from
      ⟨by linarith, le_rfl⟩)).2.2
    spatialRegion := K
    region_compact := isCompact_closedBall _ _
    region_convex := convex_closedBall _ _
    region_subset := hKsub
    image_coordinates := fun _ hw => ball_subset_closedBall hw.2
    prefix_in_image := hprefix
    continuation_in_image := fun _ hs => (hwindow hs).1.2 }⟩

end PoincareConjecture.M14

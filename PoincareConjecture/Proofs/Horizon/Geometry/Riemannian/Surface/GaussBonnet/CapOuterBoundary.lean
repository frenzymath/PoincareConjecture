import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapUnionFrontier
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CoreSupportGerms
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.OuterFaces

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

theorem independent_or_negative_smul_of_not_pos_smul {d e : Plane}
    (hd : d ≠ 0) (he : e ≠ 0) (hpos : ∀ c : ℝ, 0 < c → e ≠ c • d) :
    LinearIndependent ℝ (![d, e] : Fin 2 → Plane) ∨ ∃ c : ℝ, c < 0 ∧ e = c • d := by
  by_cases hi : LinearIndependent ℝ (![d, e] : Fin 2 → Plane)
  · exact Or.inl hi
  right
  rw [linearIndependent_fin2] at hi
  change ¬ (e ≠ 0 ∧ ∀ c : ℝ, c • e ≠ d) at hi
  have hn : ¬ ∀ c : ℝ, c • e ≠ d := fun h => hi ⟨he, h⟩
  push Not at hn
  obtain ⟨c, hc⟩ := hn
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact hd hc.symm
  have heq : e = c⁻¹ • d := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  refine ⟨c⁻¹, ?_, heq⟩
  have hn : ¬ 0 < c⁻¹ := fun hp => hpos _ hp heq
  exact lt_of_le_of_ne (le_of_not_gt hn) (inv_ne_zero hcne)

theorem union_opposite_positive_rays_eq_range (a d : Plane) {c : ℝ} (hc : c < 0) :
    ((fun t : ℝ => a + t • d) '' Ici (0 : ℝ)) ∪
      ((fun t : ℝ => a + t • (c • d)) '' Ici (0 : ℝ)) =
        range (fun t : ℝ => a + t • d) := by
  ext z
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, rfl⟩
    · refine ⟨t * c, ?_⟩
      change a + (t * c) • d = a + t • (c • d)
      rw [smul_smul]
  · rintro ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · exact Or.inl ⟨t, ht, rfl⟩
    · refine Or.inr ⟨t / c, div_nonneg_of_nonpos (le_of_not_ge ht) hc.le, ?_⟩
      change a + (t / c) • (c • d) = a + t • d
      rw [smul_smul, div_mul_cancel₀ _ hc.ne]

theorem affine_ray_range_eq_zero_set
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) {a d : Plane}
    (ha : l a = 0) (hd : d ≠ 0) (hld : l.linear d = 0) :
    range (fun t : ℝ => a + t • d) = {z | l z = 0} := by
  obtain ⟨v, hv⟩ := hl 1
  have hlv : l.linear (v - a) = 1 := by
    change l.linear (v -ᵥ a) = 1
    rw [l.linearMap_vsub, vsub_eq_sub, hv, ha, sub_zero]
  have hind : LinearIndependent ℝ (![v - a, d] : Fin 2 → Plane) := by
    rw [linearIndependent_fin2]
    refine ⟨hd, ?_⟩
    intro c he
    change c • d = v - a at he
    have h := congrArg l.linear he
    simp only [map_smul, hld, smul_zero, hlv] at h
    exact zero_ne_one h
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  have hrep (z : Plane) : z - a = b.repr (z - a) 0 • (v - a) +
      b.repr (z - a) 1 • d := by
    have h := b.sum_repr (z - a)
    simpa only [Fin.sum_univ_two, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h.symm
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change l (a + t • d) = 0
    have h := l.map_vadd a (t • d)
    simpa only [vadd_eq_add, map_smul, hld, smul_zero, ha, add_zero, add_comm] using h
  · intro hz
    change l z = 0 at hz
    have hlz : l.linear (z - a) = 0 := by
      change l.linear (z -ᵥ a) = 0
      rw [l.linearMap_vsub, vsub_eq_sub, hz, ha, sub_zero]
    have h0 := congrArg l.linear (hrep z)
    simp only [hlz, map_add, map_smul, hlv, hld, add_zero,
      smul_eq_mul, mul_one, mul_zero] at h0
    refine ⟨b.repr (z - a) 1, ?_⟩
    have hr := hrep z
    rw [← h0, zero_smul, zero_add] at hr
    change a + (b.repr (z - a) 1) • d = z
    rw [← hr]
    abel

theorem affineSegment_eventuallyEq_positive_ray {a b : Plane} (hab : b ≠ a) :
    affineSegment ℝ a b =ᶠ[𝓝 a]
      (fun t : ℝ => a + t • (b - a)) '' Ici (0 : ℝ) := by
  have hd : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  filter_upwards [Metric.ball_mem_nhds a hd] with z hz
  apply propext
  rw [affineSegment_eq_segment, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht.1, ?_⟩
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  · rintro ⟨t, ht, rfl⟩
    change 0 ≤ t at ht
    have hnorm : t * ‖b - a‖ < ‖b - a‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht] using hz
    refine ⟨t, ⟨ht, by nlinarith⟩, ?_⟩
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

theorem support_eventuallyEq_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} {q : X} (h : A =ᶠ[𝓝 q] B) :
    frontier A =ᶠ[𝓝 q] frontier B := by
  obtain ⟨V, hV, hVo, hqV⟩ := mem_nhds_iff.mp h
  filter_upwards [hVo.mem_nhds hqV] with z hz
  apply propext
  have he : A =ᶠ[𝓝 z] B := Filter.mem_of_superset (hVo.mem_nhds hz) hV
  change z ∈ closure A ∧ z ∉ interior A ↔ z ∈ closure B ∧ z ∉ interior B
  have hcomp : Aᶜ =ᶠ[𝓝 z] Bᶜ := by
    filter_upwards [he] with w hw
    exact congrArg Not hw
  have hi := Filter.EventuallyEq.mem_interior_iff he
  have hic := Filter.EventuallyEq.mem_interior_iff hcomp
  rw [interior_compl, interior_compl] at hic
  simpa only [mem_compl_iff, not_not] using (not_congr hic).and (not_congr hi)

theorem frontier_compl_interior_preimage_eventuallyEq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : OpenPartialHomeomorph X Y) (A : Set Y)
    (hA : IsClosed A) (hregular : closure (interior A) = A)
    {q : X} (hq : q ∈ F.source) :
    frontier ((interior (F ⁻¹' A))ᶜ) =ᶠ[𝓝 q] frontier (F ⁻¹' A) := by
  have hfront : frontier (interior A) = frontier A := by
    rw [frontier, interior_interior, hregular, frontier, hA.closure_eq]
  have hi : interior (F ⁻¹' A) =ᶠ[𝓝 q] F ⁻¹' interior A := by
    filter_upwards [F.open_source.mem_nhds hq] with z hz
    have h := congrArg (fun K : Set X => z ∈ K) (F.preimage_interior A)
    change (z ∈ interior (F ⁻¹' A)) = (F z ∈ interior A)
    simpa only [mem_inter_iff, hz, true_and, mem_preimage] using h.symm
  have hf := support_eventuallyEq_frontier hi
  rw [frontier_compl]
  filter_upwards [hf, F.open_source.mem_nhds hq] with z hzf hz
  have h₁ := congrArg (fun K : Set X => z ∈ K) (F.preimage_frontier (interior A))
  have h₂ := congrArg (fun K : Set X => z ∈ K) (F.preimage_frontier A)
  simp only [mem_inter_iff, hz, true_and, mem_preimage, hfront] at h₁ h₂
  exact hzf.trans (h₁.symm.trans h₂)

private theorem not_pos_smul_of_disjoint_straight_paths
    {X : Type*} (F : Plane → X) (a d e : Plane) (γ δ : ℝ → X)
    (hγ : ∀ t, γ t = F (a + t • d))
    (hδ : ∀ t, δ t = F (a + t • e))
    (hne : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, γ t ≠ δ u)
    {c : ℝ} (hc : 0 < c) : e ≠ c • d := by
  intro he
  let t : ℝ := 1 / (c + 1)
  let u : ℝ := c * t
  have htpos : 0 < t := one_div_pos.mpr (by linarith)
  have hupos : 0 < u := mul_pos hc htpos
  have htu : t + u = 1 := by
    dsimp [u, t]
    field_simp
    ring
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨htpos, by linarith⟩
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨hupos, by linarith⟩
  apply hne u hu t ht
  rw [hγ, hδ, he, smul_smul]
  congr 2
  change (c * t) • d = (t * c) • d
  rw [mul_comm c t]

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem closure_interior_union :
    closure (interior (⋃ s, (B.face s).carrier)) = ⋃ s, (B.face s).carrier := by
  apply Poincare.Topology.closure_interior_iUnion_of_regular_closed
    (fun s => (B.face s).carrier) (fun s => (B.face s).isClosed_carrier)
  intro s
  rw [B.carrier_eq]
  exact coordinate_triangle_closure_interior _ _ (B.triangle_subset_source s)

omit [T2Space S] in
theorem sector_first_tip_eq (i j : Bool) :
    P.sectorCoordinates (i, j) (B.scale, 0) = B.firstOuterTip i := by
  have h := B.first_map (i, j) 1 (by simp)
  rw [B.boundary_map] at h
  rw [← B.coordinate_first_outer_tip i j]
  simpa [affineChartSegment, Fin.succAbove, Fin.lt_def] using h.symm

omit [T2Space S] in
theorem sector_second_tip_eq (i j : Bool) :
    P.sectorCoordinates (j, i) (0, B.scale) = B.secondOuterTip i := by
  have h := B.second_map (j, i) 1 (by simp)
  rw [B.boundary_map] at h
  rw [← B.coordinate_second_outer_tip i j]
  simpa [affineChartSegment] using h.symm

omit [T2Space S] in
theorem chord_zero_eq_firstOuterTip (i j : Bool) :
    ((B.face (i, j)).boundary 0).map 0 = B.firstOuterTip i := by
  rw [B.boundary_map]
  simpa [Function.comp_apply, affineChartSegment, Fin.succAbove, Fin.lt_def]
    using B.coordinate_first_outer_tip i j

omit [T2Space S] in
theorem chord_one_eq_secondOuterTip (i j : Bool) :
    ((B.face (j, i)).boundary 0).map 1 = B.secondOuterTip i := by
  rw [B.boundary_map]
  simpa [Function.comp_apply, affineChartSegment] using B.coordinate_second_outer_tip i j

theorem frontier_union_eventuallyEq_first_chords (i : Bool) :
    frontier (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (B.firstOuterTip i)]
      ⋃ j : Bool, ((B.face (i, j)).boundary 0).map '' Icc (0 : ℝ) 1 := by
  have havoid : ∀ᶠ z in 𝓝 (B.firstOuterTip i), ∀ s : Bool × Bool,
      s.1 ≠ i → z ∉ (B.face s).carrier := by
    apply Filter.eventually_all.mpr
    intro s
    by_cases hs : s.1 = i
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hs))
    · have hn := (B.firstOuterTip_mem_carrier_iff i s).not.mpr hs
      filter_upwards [(B.face s).isClosed_carrier.isOpen_compl.mem_nhds hn] with z hz
      exact fun _ => hz
  filter_upwards [havoid] with z hz
  apply propext
  rw [B.frontier_union_eq_chords]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.mp h
    have he : s.1 = i := by
      by_contra hn
      exact hz s hn ((B.face s).isClosed_carrier.frontier_subset
        ((B.face s).boundary_image_subset_frontier 0 hs))
    exact mem_iUnion.mpr ⟨s.2, by simpa only [← he] using hs⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨(i, j), hj⟩

theorem frontier_union_eventuallyEq_second_chords (i : Bool) :
    frontier (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (B.secondOuterTip i)]
      ⋃ j : Bool, ((B.face (j, i)).boundary 0).map '' Icc (0 : ℝ) 1 := by
  have havoid : ∀ᶠ z in 𝓝 (B.secondOuterTip i), ∀ s : Bool × Bool,
      s.2 ≠ i → z ∉ (B.face s).carrier := by
    apply Filter.eventually_all.mpr
    intro s
    by_cases hs : s.2 = i
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hs))
    · have hn := (B.secondOuterTip_mem_carrier_iff i s).not.mpr hs
      filter_upwards [(B.face s).isClosed_carrier.isOpen_compl.mem_nhds hn] with z hz
      exact fun _ => hz
  filter_upwards [havoid] with z hz
  apply propext
  rw [B.frontier_union_eq_chords]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.mp h
    have he : s.2 = i := by
      by_contra hn
      exact hz s hn ((B.face s).isClosed_carrier.frontier_subset
        ((B.face s).boundary_image_subset_frontier 0 hs))
    exact mem_iUnion.mpr ⟨s.1, by simpa only [← he] using hs⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨(j, i), hj⟩

omit [T2Space S] in

theorem chart_frontier_union_eventuallyEq_incident_segments
    (v : S) (s : Bool → Bool × Bool) (q : S)
    (hchart : ∀ j, x (s j) = v)
    (hq : q ∈ (chartAt Plane v).source)
    (hfront : frontier (⋃ i, (B.face i).carrier) =ᶠ[𝓝 q]
      ⋃ j, ((B.face (s j)).boundary 0).map '' Icc (0 : ℝ) 1) :
    frontier ((chartAt Plane v).symm ⁻¹' (⋃ i, (B.face i).carrier)) =ᶠ[
      𝓝 (chartAt Plane v q)]
      ⋃ j, affineSegment ℝ
        (chartAt Plane v (P.sectorCoordinates (s j) (B.scale, 0)))
        (chartAt Plane v (P.sectorCoordinates (s j) (0, B.scale))) := by
  let F := chartAt Plane v
  have he : F.symm (F q) = q := F.left_inv hq
  have ht : F q ∈ F.target := F.map_source hq
  have hcont : Tendsto F.symm (𝓝 (F q)) (𝓝 q) := by
    simpa only [he] using (F.continuousAt_symm ht).tendsto
  have hg := hfront.comp_tendsto hcont
  have hchord (j : Bool) : ((B.face (s j)).boundary 0).map '' Icc (0 : ℝ) 1 =
      F.symm '' affineSegment ℝ
        (F (P.sectorCoordinates (s j) (B.scale, 0)))
        (F (P.sectorCoordinates (s j) (0, B.scale))) := by
    simpa only [hchart, F] using B.chord_image (s j)
  have htarget (j : Bool) : affineSegment ℝ
        (F (P.sectorCoordinates (s j) (B.scale, 0)))
        (F (P.sectorCoordinates (s j) (0, B.scale))) ⊆ F.target := by
    simpa only [hchart, F] using B.chord_segment_subset_chart_target (s j)
  filter_upwards [hg, F.open_target.mem_nhds ht] with z hz hzt
  apply propext
  have hf : z ∈ frontier (F.symm ⁻¹' (⋃ i, (B.face i).carrier)) ↔
      F.symm z ∈ frontier (⋃ i, (B.face i).carrier) := by
    have h := congrArg (fun K : Set Plane => z ∈ K) (F.symm.preimage_frontier
      (⋃ i, (B.face i).carrier))
    exact propext_iff.mp (by
      simpa only [mem_inter_iff, F.symm_source, hzt, true_and, mem_preimage] using h.symm)
  change frontier (⋃ i, (B.face i).carrier) (F.symm z) =
    (⋃ j, ((B.face (s j)).boundary 0).map '' Icc (0 : ℝ) 1) (F.symm z) at hz
  refine hf.trans ((propext_iff.mp hz).trans ?_)
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    rw [hchord j] at hj
    obtain ⟨w, hw, hew⟩ := hj
    exact mem_iUnion.mpr ⟨j, F.symm.injOn (htarget j hw) hzt hew ▸ hw⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, (hchord j).symm ▸ ⟨z, hj, rfl⟩⟩

theorem chart_frontier_union_eventuallyEq_first_rays (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v) :
    let a := chartAt Plane v (B.firstOuterTip i)
    frontier ((chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier)) =ᶠ[𝓝 a]
      ⋃ j : Bool, (fun t : ℝ => a + t •
        (chartAt Plane v (B.secondOuterTip j) - a)) '' Ici (0 : ℝ) := by
  let F := chartAt Plane v
  have hq : B.firstOuterTip i ∈ F.source := by
    have h := B.carrier_subset_chart (i, true)
      ((B.firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl)
    simpa only [hchart, F] using h
  have hs := B.chart_frontier_union_eventuallyEq_incident_segments v
    (fun j => (i, j)) (B.firstOuterTip i) hchart hq
    (B.frontier_union_eventuallyEq_first_chords i)
  simp only [B.sector_first_tip_eq, B.sector_second_tip_eq] at hs
  have hr : ∀ᶠ z in 𝓝 (F (B.firstOuterTip i)), ∀ j : Bool,
      affineSegment ℝ (F (B.firstOuterTip i)) (F (B.secondOuterTip j)) z =
        ((fun t : ℝ => F (B.firstOuterTip i) + t •
          (F (B.secondOuterTip j) - F (B.firstOuterTip i))) '' Ici (0 : ℝ)) z := by
    apply Filter.eventually_all.mpr
    intro j
    apply affineSegment_eventuallyEq_positive_ray
    have h := B.chord_chart_endpoints_ne (i, j)
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq] at h
    exact Ne.symm h
  filter_upwards [hs, hr] with z hsz hrz
  rw [hsz]
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, (propext_iff.mp (hrz j)).mp hj⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, (propext_iff.mp (hrz j)).mpr hj⟩

theorem chart_frontier_union_eventuallyEq_second_rays (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v) :
    let a := chartAt Plane v (B.secondOuterTip i)
    frontier ((chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier)) =ᶠ[𝓝 a]
      ⋃ j : Bool, (fun t : ℝ => a + t •
        (chartAt Plane v (B.firstOuterTip j) - a)) '' Ici (0 : ℝ) := by
  let F := chartAt Plane v
  have hq : B.secondOuterTip i ∈ F.source := by
    have h := B.carrier_subset_chart (true, i)
      ((B.secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl)
    simpa only [hchart, F] using h
  have hs := B.chart_frontier_union_eventuallyEq_incident_segments v
    (fun j => (j, i)) (B.secondOuterTip i) hchart hq
    (B.frontier_union_eventuallyEq_second_chords i)
  simp only [B.sector_first_tip_eq, B.sector_second_tip_eq] at hs
  have hr : ∀ᶠ z in 𝓝 (F (B.secondOuterTip i)), ∀ j : Bool,
      affineSegment ℝ (F (B.firstOuterTip j)) (F (B.secondOuterTip i)) z =
        ((fun t : ℝ => F (B.secondOuterTip i) + t •
          (F (B.firstOuterTip j) - F (B.secondOuterTip i))) '' Ici (0 : ℝ)) z := by
    apply Filter.eventually_all.mpr
    intro j
    rw [affineSegment_comm]
    apply affineSegment_eventuallyEq_positive_ray
    have h := B.chord_chart_endpoints_ne (j, i)
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq] at h
    exact h
  filter_upwards [hs, hr] with z hsz hrz
  rw [hsz]
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, (propext_iff.mp (hrz j)).mp hj⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, (propext_iff.mp (hrz j)).mpr hj⟩

theorem first_outer_chords_not_pos_smul (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v) {c : ℝ} (hc : 0 < c) :
    chartAt Plane v (B.secondOuterTip true) - chartAt Plane v (B.firstOuterTip i) ≠
      c • (chartAt Plane v (B.secondOuterTip false) -
        chartAt Plane v (B.firstOuterTip i)) := by
  let F := chartAt Plane v
  let a := F (B.firstOuterTip i)
  have hp (j : Bool) (t : ℝ) : ((B.face (i, j)).boundary 0).map t =
      F.symm (a + t • (F (B.secondOuterTip j) - a)) := by
    rw [B.chord_map]
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq]
    congr 1
    dsimp [a, F]
    module
  apply not_pos_smul_of_disjoint_straight_paths F.symm a
    (F (B.secondOuterTip false) - a) (F (B.secondOuterTip true) - a)
    (((B.face (i, false)).boundary 0).map) (((B.face (i, true)).boundary 0).map)
    (hp false) (hp true) _ hc
  intro t ht u hu he
  have hm : ((B.face (i, false)).boundary 0).map t ∈ (B.face (i, true)).carrier := by
    rw [he]
    exact (B.face (i, true)).isClosed_carrier.frontier_subset
      ((B.face (i, true)).boundary_image_subset_frontier 0 ⟨u, Ioo_subset_Icc_self hu, rfl⟩)
  have hi := (B.open_chord_mem_carrier_iff (i, false) (i, true) ht).mp hm
  exact Bool.noConfusion (congrArg Prod.snd hi)

theorem second_outer_chords_not_pos_smul (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v) {c : ℝ} (hc : 0 < c) :
    chartAt Plane v (B.firstOuterTip true) - chartAt Plane v (B.secondOuterTip i) ≠
      c • (chartAt Plane v (B.firstOuterTip false) -
        chartAt Plane v (B.secondOuterTip i)) := by
  let F := chartAt Plane v
  let a := F (B.secondOuterTip i)
  have hp (j : Bool) (t : ℝ) : ((B.face (j, i)).boundary 0).map (1 - t) =
      F.symm (a + t • (F (B.firstOuterTip j) - a)) := by
    rw [B.chord_map]
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq]
    congr 1
    dsimp [a, F]
    module
  apply not_pos_smul_of_disjoint_straight_paths F.symm a
    (F (B.firstOuterTip false) - a) (F (B.firstOuterTip true) - a)
    (fun t => ((B.face (false, i)).boundary 0).map (1 - t))
    (fun t => ((B.face (true, i)).boundary 0).map (1 - t)) (hp false) (hp true) _ hc
  intro t ht u hu he
  have htr : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hur : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hm : ((B.face (false, i)).boundary 0).map (1 - t) ∈ (B.face (true, i)).carrier := by
    rw [he]
    exact (B.face (true, i)).isClosed_carrier.frontier_subset
      ((B.face (true, i)).boundary_image_subset_frontier 0 ⟨1 - u, hur, rfl⟩)
  have hi := (B.open_chord_mem_carrier_iff (false, i) (true, i) htr).mp hm
  exact Bool.noConfusion (congrArg Prod.fst hi)

end ChartCircleArrangementVertexPatch.VertexCapFaces

end PoincareConjecture.Topology.Surface

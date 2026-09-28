import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.RefinedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.InitialFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Classical
open scoped Topology Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space S] in

theorem vertex_mem_frontier (v : Fin (B.interface.count + 1) × Bool) :
    B.vertex v ∈ frontier B.carrier := by
  obtain ⟨i, hi⟩ : ∃ i : Fin B.interface.count, v.1 = i.castSucc ∨ v.1 = i.succ := by
    by_cases h : v.1.val < B.interface.count
    · exact ⟨⟨v.1.val, h⟩, Or.inl (Fin.ext rfl)⟩
    · refine ⟨B.lastCell, Or.inr (Fin.ext ?_)⟩
      have hn := B.interface.count_pos
      have hv := v.1.isLt
      simp only [lastCell, Fin.val_succ]
      omega
  have ht : B.cut v.1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) := by
    rcases hi with hi | hi
    · rw [hi]
      exact left_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
    · rw [hi]
      exact right_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
  have hh : B.height (B.cut v.1) = B.interface.height v.1 := by
    rw [B.height_eq_upperGraph ht]
    rcases hi with hi | hi
    · rw [hi]
      exact (B.upperGraph_endpoints i).1
    · rw [hi]
      exact (B.upperGraph_endpoints i).2
  have hunit : B.cut v.1 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [B.cut_first] using B.cut_strictMono.monotone (Fin.zero_le v.1)
    · simpa only [B.cut_last] using B.cut_strictMono.monotone (Fin.le_last v.1)
  apply B.coordinate_outer_mem_frontier
  · rw [B.band_eq_subgraph]
    simp only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, hh]
    refine ⟨hunit, ?_⟩
    have hpos := (B.interface.vertex_height_bounds v.1).1
    cases v.2 <;> simp [hpos.le]
  · simp only [collarParameterEquiv.apply_symm_apply, hh]
    cases v.2 <;> simp

omit [T2Space S] in

theorem incident_face_same_side_eq {q : S}
    (hnew : ∀ v, q ≠ B.vertex v) (s : Bool) {i j : Fin B.interface.count}
    (hi : q ∈ (B.face (i, s)).carrier) (hj : q ∈ (B.face (j, s)).carrier) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · exact this hi hj hlt
    · exact heq
    · exact (this hj hi hgt).symm
  have hp := (B.pair i).parameter_mem hi
  have hq := (B.pair j).parameter_mem hj
  have hle : i.succ ≤ j.castSucc := hij
  have hsame : (collarParameterEquiv (B.coordinates.symm q)).1 = B.cut i.succ :=
    le_antisymm hp.1.2 ((B.cut_strictMono.monotone hle).trans hq.1.1)
  have hsame' : (collarParameterEquiv (B.coordinates.symm q)).1 = B.cut j.castSucc :=
    le_antisymm (hp.1.2.trans (B.cut_strictMono.monotone hle)) hq.1.1
  cases s
  · exact False.elim (hnew (j.castSucc, false) ((B.pair j).lower_left_vertex hj hsame'))
  · apply False.elim (hnew (i.succ, true) ?_)
    simpa only [vertex, if_true, (B.upperGraph_endpoints i).2] using
      (B.pair i).upper_right_vertex hi hsame

private theorem mem_interior_face_of_unique {q : S} (hq : q ∈ interior B.carrier)
    (p : Fin B.interface.count × Bool)
    (hunique : ∀ r, q ∈ (B.face r).carrier → r = p) :
    q ∈ interior (B.face p).carrier := by
  have havoid : ∀ᶠ z in 𝓝 q, ∀ r, r ≠ p → z ∉ (B.face r).carrier := by
    apply Filter.eventually_all.mpr
    intro r
    by_cases hr : r = p
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hr)
    · have he := (B.face r).isClosed_carrier.isOpen_compl.mem_nhds
        (fun h => hr (hunique r h))
      filter_upwards [he] with z hz
      exact fun _ => hz
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [mem_interior_iff_mem_nhds.mp hq, havoid] with z hz havoid
  obtain ⟨r, hr⟩ := mem_iUnion.mp hz
  by_cases he : r = p
  · simpa only [he] using hr
  · exact False.elim (havoid r he hr)

private theorem not_mem_other_face_of_interior {q : S}
    (hnew : ∀ v, q ≠ B.vertex v) (p r : Fin B.interface.count × Bool) (hrp : r ≠ p)
    (hq : q ∈ interior (B.face p).carrier) : q ∉ (B.face r).carrier := by
  intro hr
  rcases B.face_intersection p r (Ne.symm hrp) with ⟨k, l, _, hinter⟩ | ⟨v, hv⟩
  · have he : q ∈ ((B.face p).boundary k).map '' Icc (0 : ℝ) 1 :=
      hinter ▸ ⟨interior_subset hq, hr⟩
    exact ((B.face p).boundary_image_subset_frontier k he).2 hq
  · exact hnew v (hv ⟨interior_subset hq, hr⟩)

omit [T2Space S] in
private theorem face_coordinate_mem_interior {p : Fin B.interface.count × Bool} {z : Plane}
    (hz : z ∈ convexHull ℝ (range (B.faceBasis p)))
    (hq : B.faceCoordinates p z ∈ interior (B.face p).carrier) :
    z ∈ interior (convexHull ℝ (range (B.faceBasis p))) := by
  let E := B.faceCoordinates p
  have hs : z ∈ E.source := B.face_triangle_subset_source p hz
  have hopen : IsOpen (E.source ∩ E ⁻¹' interior (B.face p).carrier) :=
    E.continuousOn.isOpen_inter_preimage E.open_source isOpen_interior
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (hopen.mem_nhds ⟨hs, hq⟩)
  intro w hw
  rw [B.face_carrier_eq_coordinates] at hw
  obtain ⟨v, hv, he⟩ := interior_subset hw.2
  exact E.injOn (B.face_triangle_subset_source p hv) hw.1 he ▸ hv

omit [T2Space S] in
private theorem face_coordinate_image_mem_interior {p : Fin B.interface.count × Bool} {z : Plane}
    (hz : z ∈ interior (convexHull ℝ (range (B.faceBasis p)))) :
    B.faceCoordinates p z ∈ interior (B.face p).carrier := by
  have hopen := (B.faceCoordinates p).isOpen_image_of_subset_source isOpen_interior
    ((interior_subset (s := convexHull ℝ (range (B.faceBasis p)))).trans
      (B.face_triangle_subset_source p))
  apply hopen.subset_interior_iff.mpr _ (mem_image_of_mem _ hz)
  rw [B.face_carrier_eq_coordinates]
  exact image_mono interior_subset

omit [T2Space S] in

theorem refined_face_contribution_of_band_interior
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (p : Fin B.interface.count × Bool) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {q : S} (hq : q ∈ interior B.carrier)
    (hused : q ∈ (B.face p).carrier →
      ∃ (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).Triangle)
        (v : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).Vertex),
        v ∈ u.1 ∧ B.faceCoordinates p
          (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).position v) = q) :
    meshVertexAngleContribution g (B.faceCoordinates p)
      ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines) q =
      if q ∈ (B.face p).carrier then
        if q ∈ interior (B.face p).carrier then 2 * Real.pi else Real.pi else 0 := by
  split_ifs with hp hi
  · obtain ⟨u, v, hv, heq⟩ := hused hp
    rw [← heq]
    apply single_refineByLines_interior_vertex_fan g (B.faceCoordinates p)
      (B.faceBasis p) lines (B.smooth_faceCoordinates hF p)
      (B.smooth_faceCoordinates_symm hFi p) (B.face_triangle_subset_source p) u v hv
    rw [TriangleMesh.refineByLines_support, TriangleMesh.single_support]
    apply B.face_coordinate_mem_interior
    · have hm := meshTriangleBasis_subset_support
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines) u
        (subset_convexHull ℝ _ (by rw [range_meshTriangleBasis]; exact ⟨v, hv, rfl⟩))
      simpa only [TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hm
    · exact heq ▸ hi
  · obtain ⟨u, v, hv, heq⟩ := hused hp
    rw [← heq]
    apply single_refineByLines_new_boundary_vertex_fan g (B.faceCoordinates p)
      (B.faceBasis p) lines (B.smooth_faceCoordinates hF p)
      (B.smooth_faceCoordinates_symm hFi p) (B.face_triangle_subset_source p) u v hv
    · exact fun hz => hi (heq ▸ B.face_coordinate_image_mem_interior hz)
    · rintro ⟨k, hk⟩
      have hvq : B.vertex (B.cornerVertexIndex p k) = q :=
        (B.face_corner_eq_vertex p k).symm.trans (congrArg (B.faceCoordinates p) hk |>.trans heq)
      exact (hvq ▸ B.vertex_mem_frontier (B.cornerVertexIndex p k)).2 hq
  · exact B.refined_contribution_eq_zero_of_not_mem_carrier g p lines hp

theorem interior_refined_vertex_fan
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    {q : S} (hq : q ∈ interior B.carrier)
    (hused : ∀ p, q ∈ (B.face p).carrier →
      ∃ (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
        (v : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
        v ∈ u.1 ∧ B.faceCoordinates p
          (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position v) = q) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)) q) =
      2 * Real.pi := by
  have hnew (v) : q ≠ B.vertex v := fun he => (he ▸ B.vertex_mem_frontier v).2 hq
  simp_rw [B.refined_face_contribution_of_band_interior g hF hFi _ _ hq (hused _)]
  by_cases hi : ∃ p, q ∈ interior (B.face p).carrier
  · obtain ⟨p, hp⟩ := hi
    rw [Finset.sum_eq_single p]
    · simp only [if_pos (interior_subset hp), if_pos hp]
    · intro r _ hr
      rw [if_neg (B.not_mem_other_face_of_interior hnew p r hr hp)]
    · simp
  · have hnint (p) : q ∉ interior (B.face p).carrier := fun hp => hi ⟨p, hp⟩
    simp_rw [if_neg (hnint _)]
    have hside (s : Bool) : ∃ i, q ∈ (B.face (i, s)).carrier := by
      by_contra hnone
      have hnot (i) : q ∉ (B.face (i, s)).carrier := fun hi => hnone ⟨i, hi⟩
      obtain ⟨p, hp⟩ := mem_iUnion.mp (interior_subset hq)
      apply hnint p
      apply B.mem_interior_face_of_unique hq p
      rintro ⟨i, t⟩ ht
      have hps : p.2 ≠ s := by
        intro he
        exact hnot p.1 (he ▸ hp)
      have hts : t ≠ s := fun he => hnot i (he ▸ ht)
      have htp : t = p.2 := by
        cases hs : s <;> cases ht' : t <;> cases hp' : p.2 <;> simp_all
      apply Prod.ext
      · exact B.incident_face_same_side_eq hnew t ht (htp.symm ▸ hp)
      · exact htp
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hs (s : Bool) : (∑ i : Fin B.interface.count,
        if q ∈ (B.face (i, s)).carrier then Real.pi else 0) = Real.pi := by
      obtain ⟨i, hi⟩ := hside s
      rw [Finset.sum_eq_single i]
      · exact if_pos hi
      · intro j _ hji
        exact if_neg (fun hj => hji (B.incident_face_same_side_eq hnew s hj hi))
      · simp
    simp_rw [hs]
    simp only [Fintype.sum_bool]
    ring

end PoincareConjecture.Topology.Surface.ObliqueBandFaces

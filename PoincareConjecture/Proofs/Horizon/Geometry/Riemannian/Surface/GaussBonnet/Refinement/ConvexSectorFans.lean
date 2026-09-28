import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.GeneralBoundaryFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem wedge_restriction_support_subset (M : TriangleMesh)
    (l m : Plane →ᵃ[ℝ] ℝ) :
    (M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ l z ∧ 0 ≤ m z})).toPlaneComplex.support ⊆
        {z | 0 ≤ l z ∧ 0 ≤ m z} := by
  intro z hz
  rw [TriangleMesh.toPlaneComplex_support] at hz
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
  exact ((M.mem_restrictTriangles_triangles _).mp ht).2 hzt

theorem mem_wedge_restriction_of_mem_interior (M : TriangleMesh)
    (l m : Plane →ᵃ[ℝ] ℝ) (hl : M.IsMonochromatic l) (hm : M.IsMonochromatic m)
    {v : Plane} (hlv : 0 < l.linear v) (hmv : 0 < m.linear v)
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support)
    (hql : 0 ≤ l q) (hqm : 0 ≤ m q) :
    q ∈ (M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ l z ∧ 0 ≤ m z})).toPlaneComplex.support := by
  let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
    {z | 0 ≤ l z ∧ 0 ≤ m z})
  have hstrict {z : Plane} (hz : z ∈ M.toPlaneComplex.support)
      (hzl : 0 < l z) (hzm : 0 < m z) : z ∈ N.toPlaneComplex.support := by
    rw [TriangleMesh.toPlaneComplex_support] at hz ⊢
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨t, (M.mem_restrictTriangles_triangles _).mpr ⟨ht, ?_⟩, hzt⟩
    have hlpos : M.triangleCarrier t ⊆ {z | 0 ≤ l z} := by
      rcases hl.triangleCarrier_halfspace M ⟨t, ht⟩ with hpos | hneg
      · exact hpos
      · exact False.elim (not_lt_of_ge (hneg z hzt) hzl)
    have hmpos : M.triangleCarrier t ⊆ {z | 0 ≤ m z} := by
      rcases hm.triangleCarrier_halfspace M ⟨t, ht⟩ with hpos | hneg
      · exact hpos
      · exact False.elim (not_lt_of_ge (hneg z hzt) hzm)
    exact fun w hw => ⟨hlpos hw, hmpos hw⟩
  let path : ℝ → Plane := fun t => q + t • v
  have hp : Continuous path := by dsimp [path]; fun_prop
  have hp0 : path 0 = q := by simp [path]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ interior M.toPlaneComplex.support :=
    hp.continuousAt.eventually (isOpen_interior.mem_nhds (hp0 ▸ hq))
  have hpathN : ∀ᶠ t in 𝓝[>] (0 : ℝ), path t ∈ N.toPlaneComplex.support := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ht htpos
    apply hstrict (interior_subset ht)
    · have he : l (path t) = t * l.linear v + l q := by
        simpa only [path, vadd_eq_add, add_comm, map_smul, smul_eq_mul] using l.map_vadd q (t • v)
      rw [he]
      exact add_pos_of_pos_of_nonneg (mul_pos htpos hlv) hql
    · have he : m (path t) = t * m.linear v + m q := by
        simpa only [path, vadd_eq_add, add_comm, map_smul, smul_eq_mul] using m.map_vadd q (t • v)
      rw [he]
      exact add_pos_of_pos_of_nonneg (mul_pos htpos hmv) hqm
  have hpq : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 q) :=
    hp0 ▸ hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact N.toPlaneComplex.isCompact_support.isClosed.mem_of_tendsto hpq hpathN

theorem wedge_restriction_support_eventuallyEq (M : TriangleMesh)
    (l m : Plane →ᵃ[ℝ] ℝ) (hl : M.IsMonochromatic l) (hm : M.IsMonochromatic m)
    {v : Plane} (hlv : 0 < l.linear v) (hmv : 0 < m.linear v)
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support) :
    (M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ l z ∧ 0 ≤ m z})).toPlaneComplex.support =ᶠ[𝓝 q]
        {z | 0 ≤ l z ∧ 0 ≤ m z} := by
  filter_upwards [isOpen_interior.mem_nhds hq] with z hz
  apply propext
  exact ⟨fun h => wedge_restriction_support_subset M l m h,
    fun h => mem_wedge_restriction_of_mem_interior M l m hl hm hlv hmv hz h.1 h.2⟩

theorem wedge_restriction_edge_exists_other_parent
    (M : TriangleMesh) (l m : Plane →ᵃ[ℝ] ℝ)
    (hl : M.IsMonochromatic l) (hm : M.IsMonochromatic m)
    (t : (M.restrictTriangles (fun s => M.triangleCarrier s ⊆
      {z | 0 ≤ l z ∧ 0 ≤ m z})).Triangle)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) (ham : m (M.position a) = 0)
    (hbl : 0 < l (M.position b)) (hbm : 0 < m (M.position b)) :
    ∃ u : (M.restrictTriangles (fun s => M.triangleCarrier s ⊆
      {z | 0 ≤ l z ∧ 0 ≤ m z})).Triangle,
      u ≠ t ∧ a ∈ u.1 ∧ b ∈ u.1 := by
  let N := M.restrictTriangles (fun s => M.triangleCarrier s ⊆
    {z | 0 ≤ l z ∧ 0 ≤ m z})
  let v := M.position b - M.position a
  have hlv : 0 < l.linear v := by
    change 0 < l.linear (M.position b -ᵥ M.position a)
    rw [l.linearMap_vsub, vsub_eq_sub, hal, sub_zero]
    exact hbl
  have hmv : 0 < m.linear v := by
    change 0 < m.linear (M.position b -ᵥ M.position a)
    rw [m.linearMap_vsub, vsub_eq_sub, ham, sub_zero]
    exact hbm
  let path : ℝ → Plane := AffineMap.lineMap (M.position a) (M.position b)
  have hp : Continuous path := by dsimp [path]; fun_prop
  have hint : ∀ᶠ s in 𝓝 (0 : ℝ), path s ∈ interior M.toPlaneComplex.support :=
    hp.continuousAt.eventually (isOpen_interior.mem_nhds
      (by simpa only [path, AffineMap.lineMap_apply_zero] using haint))
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      0 < s ∧ s < 1 ∧ path s ∈ interior M.toPlaneComplex.support := by
    have hlt : ∀ᶠ s in 𝓝 (0 : ℝ), s < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [hint.filter_mono nhdsWithin_le_nhds,
      hlt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hs hslt hspos
    exact ⟨hspos, hslt, hs⟩
  obtain ⟨s, hspos, hslt, hsint⟩ := hnear.exists
  have hsl : 0 < l (path s) := by
    simp only [path, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      hal, mul_zero, zero_add]
    exact mul_pos hspos hbl
  have hsm : 0 < m (path s) := by
    simp only [path, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      ham, mul_zero, zero_add]
    exact mul_pos hspos hbm
  have hN : path s ∈ interior N.toPlaneComplex.support := by
    apply (isOpen_interior.inter ((isOpen_Ioi.preimage l.continuous_of_finiteDimensional).inter
      (isOpen_Ioi.preimage m.continuous_of_finiteDimensional))).subset_interior_iff.mpr
      (show interior M.toPlaneComplex.support ∩ (l ⁻¹' Ioi (0 : ℝ) ∩ m ⁻¹' Ioi (0 : ℝ)) ⊆
        N.toPlaneComplex.support from fun z hz =>
          mem_wedge_restriction_of_mem_interior M l m hl hm hlv hmv hz.1 hz.2.1.le hz.2.2.le)
    exact ⟨hsint, hsl, hsm⟩
  exact mesh_edge_exists_other_parent_of_interior N t ha hb hab
    (by rw [openSegment_eq_image_lineMap]; exact ⟨s, ⟨hspos, hslt⟩, rfl⟩) hN

theorem mesh_usedVertex_not_mem_open_edge (M : TriangleMesh)
    (t u : M.Triangle) {a b c : M.Vertex}
    (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) (hc : c ∈ u.1) :
    M.position c ∉ openSegment ℝ (M.position a) (M.position b) := by
  intro hseg
  have hct : c ∈ t.1 := mesh_usedVertex_mem_triangle_of_mem_hull M t u hc
    ((convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by rw [range_meshTriangleBasis]; exact ⟨a, ha, rfl⟩))
      (subset_convexHull ℝ _ (by rw [range_meshTriangleBasis]; exact ⟨b, hb, rfl⟩))
      (openSegment_subset_segment ℝ _ _ hseg))
  obtain ⟨d, hd0, hd1, hdr⟩ := exists_meshTriangleBasis_with_edge M t ha hb hab
  have hcr : M.position c ∈ range d := by
    rw [hdr, range_meshTriangleBasis]
    exact ⟨c, hct, rfl⟩
  obtain ⟨k, hk⟩ := hcr
  have hbad := affineBasis_vertex_not_mem_open_edge d 2 k
  apply hbad
  simpa only [show (2 : Fin 3).succAbove 0 = 0 from rfl,
    show (2 : Fin 3).succAbove 1 = 1 from rfl, hd0, hd1, hk] using hseg

theorem mesh_edge_endpoint_eq_of_same_positive_ray (M : TriangleMesh)
    (t u : M.Triangle) {a b c : M.Vertex}
    (hat : a ∈ t.1) (hbt : b ∈ t.1) (hab : a ≠ b)
    (hau : a ∈ u.1) (hcu : c ∈ u.1) (hac : a ≠ c)
    {r : Plane} {s v : ℝ} (hs : 0 < s) (hv : 0 < v)
    (hb : M.position b - M.position a = s • r)
    (hc : M.position c - M.position a = v • r) : b = c := by
  have hbetween {b c : M.Vertex} {s v : ℝ} (hs : 0 < s) (hsv : s < v)
      (hb : M.position b - M.position a = s • r)
      (hc : M.position c - M.position a = v • r) :
      M.position b ∈ openSegment ℝ (M.position a) (M.position c) := by
    rw [openSegment_eq_image_lineMap]
    have hv : 0 < v := hs.trans hsv
    refine ⟨s / v, ⟨div_pos hs hv, (div_lt_one hv).mpr hsv⟩, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hc, smul_smul,
      div_mul_cancel₀ s hv.ne', ← hb]
    abel
  rcases lt_trichotomy s v with hlt | heq | hgt
  · exact False.elim (mesh_usedVertex_not_mem_open_edge M u t hau hcu hac hbt
      (hbetween hs hlt hb hc))
  · apply M.position_injective
    have he := hb.trans ((congrArg (fun w : ℝ => w • r) heq).trans hc.symm)
    exact sub_left_injective he
  · exact False.elim (mesh_usedVertex_not_mem_open_edge M t u hat hbt hab hcu
      (hbetween hv hgt hc hb))

theorem halfspace_mesh_edge_parent_unique (M : TriangleMesh)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hM : M.toPlaneComplex.support ⊆ {z | 0 ≤ l z})
    (t u : M.Triangle) {a b : M.Vertex}
    (ha : a ∈ t.1) (hb : b ∈ t.1) (hau : a ∈ u.1) (hbu : b ∈ u.1)
    (hab : a ≠ b) (hal : l (M.position a) = 0) (hbl : l (M.position b) = 0) :
    t = u := by
  by_contra htu
  obtain ⟨d, hd0, hd1, hdr⟩ := exists_meshTriangleBasis_with_edge M t ha hb hab
  obtain ⟨e, he0, he1, her⟩ := exists_meshTriangleBasis_with_edge M u hau hbu hab
  have hdisj : Disjoint (interior (convexHull ℝ (range d)))
      (interior (convexHull ℝ (range e))) := by
    rw [hdr, her]
    exact mesh_common_edge_disjoint_interiors M t u htu hab ha hb hau hbu
  let q := AffineMap.lineMap (M.position a) (M.position b) (1 / 2 : ℝ)
  have hqseg : q ∈ openSegment ℝ (d 0) (d 1) := by
    rw [openSegment_eq_image_lineMap, hd0, hd1]
    exact ⟨1 / 2, by norm_num, rfl⟩
  have hint := affineTriangle_shared_edge_mem_interior_union d e
    (hd0.trans he0.symm) (hd1.trans he1.symm)
    (affineTriangle_shared_edge_coord_neg d e (hd0.trans he0.symm)
      (hd1.trans he1.symm) hdisj) hqseg
  have hqint : q ∈ interior M.toPlaneComplex.support := interior_mono
    (union_subset (by rw [hdr]; exact meshTriangleBasis_subset_support M t)
      (by rw [her]; exact meshTriangleBasis_subset_support M u)) hint
  have h := interior_mono hM hqint
  change q ∈ interior (l ⁻¹' Ici (0 : ℝ)) at h
  rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
    l.continuous_of_finiteDimensional, interior_Ici] at h
  have hqzero : l q = 0 := by
    simp [q, AffineMap.apply_lineMap, hal, hbl]
  exact (ne_of_gt h) hqzero

section OrientedSector

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

theorem convexSector_boundary_edge_angleSign
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (hM : M.toPlaneComplex.support ⊆ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    (t : M.Triangle) {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1)
    (hab : a ≠ b) (ha0 : M.position a = c 0)
    (hb1 : c.coord 1 (M.position b) = 0) (hb2 : 0 < c.coord 2 (M.position b)) :
    meshEdgeAngleSign M o L a b t =
      -((o.oangle (L (c 1 - c 0)) (L (c 2 - c 0))).sign : ℤ) := by
  let D := meshEdgeBasis M t a b ha hb hab
  have hD0 : D 0 = c 0 := (meshEdgeBasis_zero M t a b ha hb hab).trans ha0
  have hD1 : D 1 = M.position b := meshEdgeBasis_one M t a b ha hb hab
  have hD2 : D 2 ∈ M.toPlaneComplex.support := by
    apply meshTriangleBasis_subset_support M t
    rw [← range_meshEdgeBasis M t a b ha hb hab]
    exact subset_convexHull ℝ _ (mem_range_self 2)
  have h2nonneg := (hM hD2).1
  have h2pos : 0 < c.coord 1 (D 2) := by
    apply lt_of_le_of_ne h2nonneg
    intro he
    have hzero : ∀ k : Fin 3, c.coord 1 (D k) = 0 := by
      intro k
      fin_cases k
      · rw [show D ⟨0, by decide⟩ = D 0 from rfl, hD0]
        simp
      · rw [show D ⟨1, by decide⟩ = D 1 from rfl, hD1]
        exact hb1
      · exact he.symm
    have heq : c.coord 1 = 0 := AffineMap.ext_on D.tot (by
      rintro z ⟨k, rfl⟩
      exact hzero k)
    have hh := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (c 1)) heq
    simp at hh
  have hdir : M.position b - c 0 = c.coord 2 (M.position b) • (c 2 - c 0) := by
    rw [affineBasis_vsub_zero_eq c, hb1, zero_smul, zero_add]
  rw [meshEdgeAngleSign_eq_basis M o L t a b ha hb hab D (hD0.trans ha0.symm)
    (by exact hD1) (range_meshEdgeBasis M t a b ha hb hab)]
  rw [hD0, hD1, hdir, map_smul,
    o.oangle_smul_left_of_pos _ _ hb2, affineBasis_vsub_zero_eq c (D 2),
    map_add, map_smul, map_smul, add_comm,
    o.oangle_sign_smul_add_smul_right, sign_eq_one_iff.mpr h2pos, one_mul,
    o.oangle_rev, Real.Angle.sign_neg, SignType.coe_neg]

theorem convexSector_sum_edge_potential_eq_zero_or_boundary
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : M.IsMonochromatic (c.coord 1)) (h2 : M.IsMonochromatic (c.coord 2))
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V) (a : M.Vertex)
    (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (ha0 : M.position a = c 0) :
    let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    let θ := o.oangle (L (c 1 - c 0)) (L (c 2 - c 0))
    let s := ∑ b : M.Vertex, ∑ t : N.Triangle,
      meshEdgeAngleSign N o L a b t •
        o.oangle (L (c 1 - c 0)) (L (M.position b - M.position a))
    s = 0 ∨ s = -((θ.sign : ℤ) • θ) := by
  let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
    {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
  let θ := o.oangle (L (c 1 - c 0)) (L (c 2 - c 0))
  let φ : M.Vertex → Real.Angle := fun b =>
    o.oangle (L (c 1 - c 0)) (L (M.position b - M.position a))
  let edge : M.Vertex → Prop := fun b =>
    ∃ t : N.Triangle, a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b ∧ c.coord 1 (M.position b) = 0
  have hN := wedge_restriction_support_subset M (c.coord 1) (c.coord 2)
  have hbnonneg (t : N.Triangle) {b : M.Vertex} (hb : b ∈ t.1) :
      0 ≤ c.coord 1 (M.position b) ∧ 0 ≤ c.coord 2 (M.position b) :=
    ((M.mem_restrictTriangles_triangles _).mp t.2).2
      (subset_convexHull ℝ _ ⟨b, hb, rfl⟩)
  have hbdir {b : M.Vertex} (hb1 : c.coord 1 (M.position b) = 0) :
      M.position b - M.position a = c.coord 2 (M.position b) • (c 2 - c 0) := by
    rw [ha0, affineBasis_vsub_zero_eq c, hb1, zero_smul, zero_add]
  have hbpos (t : N.Triangle) {b : M.Vertex} (hb : b ∈ t.1)
      (hab : a ≠ b) (hb1 : c.coord 1 (M.position b) = 0) :
      0 < c.coord 2 (M.position b) := by
    apply lt_of_le_of_ne (hbnonneg t hb).2
    intro he
    have hh := hbdir hb1
    rw [← he, zero_smul, sub_eq_zero] at hh
    exact hab (M.position_injective hh.symm)
  have hsurj : Function.Surjective (c.coord 1) := by
    intro r
    refine ⟨AffineMap.lineMap (c 0) (c 1) r, ?_⟩
    simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hunique {b d : M.Vertex} (hb : edge b) (hd : edge d) : b = d := by
    obtain ⟨t, hat, hbt, hab, hb1⟩ := hb
    obtain ⟨u, hau, hdu, had, hd1⟩ := hd
    exact mesh_edge_endpoint_eq_of_same_positive_ray N t u hat hbt hab hau hdu had
      (hbpos t hbt hab hb1) (hbpos u hdu had hd1) (hbdir hb1) (hbdir hd1)
  have hterm {b : M.Vertex} (hb : edge b) :
      (∑ t : N.Triangle, meshEdgeAngleSign N o L a b t • φ b) =
        -((θ.sign : ℤ) • θ) := by
    obtain ⟨t, hat, hbt, hab, hb1⟩ := hb
    have hp := hbpos t hbt hab hb1
    have hφ : φ b = θ := by
      dsimp only [φ, θ]
      rw [hbdir hb1, map_smul, o.oangle_smul_right_of_pos _ _ hp]
    rw [Finset.sum_eq_single t]
    · rw [convexSector_boundary_edge_angleSign N c o L hN t hat hbt hab ha0 hb1 hp,
        hφ, neg_smul]
    · intro u _ hut
      rw [meshEdgeAngleSign]
      split_ifs with h
      · exact False.elim (hut (halfspace_mesh_edge_parent_unique N (c.coord 1) hsurj
          (fun _ hz => (hN hz).1) u t h.1 h.2.1 hat hbt hab
          (by change c.coord 1 (M.position a) = 0; rw [ha0]; simp) hb1))
      · exact zero_smul _ _
    · exact fun ht => False.elim (ht (Finset.mem_univ t))
  have hzero {b : M.Vertex} (hb : ¬edge b) :
      (∑ t : N.Triangle, meshEdgeAngleSign N o L a b t • φ b) = 0 := by
    by_cases hparents : ∃ t : N.Triangle, a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b
    · obtain ⟨t, hat, hbt, hab⟩ := hparents
      have hb1 : c.coord 1 (M.position b) ≠ 0 := fun h => hb ⟨t, hat, hbt, hab, h⟩
      by_cases hb2 : c.coord 2 (M.position b) = 0
      · have hφ : φ b = 0 := by
          dsimp only [φ]
          rw [ha0, affineBasis_vsub_zero_eq c (M.position b), hb2, zero_smul,
            add_zero, map_smul]
          exact o.oangle_smul_right_self_of_nonneg _ (hbnonneg t hbt).1
        simp only [hφ, smul_zero, Finset.sum_const_zero]
      · obtain ⟨u, hut, hau, hbu⟩ := wedge_restriction_edge_exists_other_parent
          M (c.coord 1) (c.coord 2) h1 h2 t hat hbt hab haint
          (by rw [ha0]; simp) (by rw [ha0]; simp)
          (lt_of_le_of_ne (hbnonneg t hbt).1 hb1.symm)
          (lt_of_le_of_ne (hbnonneg t hbt).2 (Ne.symm hb2))
        rw [← Finset.sum_smul, sum_meshEdgeAngleSign_eq_zero_of_two_parents
          N o L hab t u hut.symm hat hbt hau hbu, zero_smul]
    · apply Finset.sum_eq_zero
      intro t _
      rw [meshEdgeAngleSign, dif_neg (fun h => hparents ⟨t, h⟩), zero_smul]
  change (∑ b : M.Vertex, ∑ t : N.Triangle, meshEdgeAngleSign N o L a b t • φ b) = 0 ∨
    (∑ b : M.Vertex, ∑ t : N.Triangle, meshEdgeAngleSign N o L a b t • φ b) =
      -((θ.sign : ℤ) • θ)
  by_cases hex : ∃ b, edge b
  · obtain ⟨b, hb⟩ := hex
    right
    rw [Finset.sum_eq_single b]
    · exact hterm hb
    · intro d _ hdb
      exact hzero (fun hd => hdb (hunique hd hb))
    · exact fun h => False.elim (h (Finset.mem_univ b))
  · left
    exact Finset.sum_eq_zero fun b _ => hzero (fun hb => hex ⟨b, hb⟩)

theorem convexSector_sum_linearCorner_coe_eq_zero_or_angle
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : M.IsMonochromatic (c.coord 1)) (h2 : M.IsMonochromatic (c.coord 2))
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V) (hL : Function.Injective L)
    (a : M.Vertex) (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (ha0 : M.position a = c 0) :
    let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) = 0 ∨
      ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) =
        (InnerProductGeometry.angle (L (c 1 - c 0)) (L (c 2 - c 0)) : Real.Angle) := by
  let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
    {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
  have hne (i : Fin 3) (hi : i ≠ 0) : L (c i - c 0) ≠ 0 := by
    intro h
    have he := hL (h.trans (map_zero L).symm)
    exact hi (c.ind.injective (sub_eq_zero.mp he))
  have heq : ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) =
      -(∑ b : M.Vertex, ∑ t : N.Triangle, meshEdgeAngleSign N o L a b t •
        o.oangle (L (c 1 - c 0)) (L (M.position b - M.position a))) := by
    have hcoe : ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) =
        ∑ t : N.Triangle, (meshLinearCorner N L a t : Real.Angle) :=
      map_sum Real.Angle.coeHom _ _
    rw [hcoe]
    simp_rw [meshLinearCorner_coe_eq_neg_sum_edge_potential N o L hL a _
      (L (c 1 - c 0)) (hne 1 (by decide))]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    rfl
  have hangle := angle_coe_eq_sign_smul_oangle o (hne 1 (by decide))
    (hne 2 (by decide)) (affineBasis_linear_angle_mem_Ioo L hL c)
  rcases convexSector_sum_edge_potential_eq_zero_or_boundary M c h1 h2 o L a haint ha0
    with hz | hθ
  · exact Or.inl (heq.trans (by rw [hz, neg_zero]))
  · exact Or.inr (heq.trans (by rw [hθ, neg_neg, ← hangle]))

end OrientedSector

section MetricSector

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem convexSector_restriction_support_eventuallyEq
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : M.IsMonochromatic (c.coord 1)) (h2 : M.IsMonochromatic (c.coord 2))
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support) :
    (M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})).toPlaneComplex.support =ᶠ[𝓝 q]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  let v := (c 1 - c 0) + (c 2 - c 0)
  have hv (i : Fin 3) (hi : i = 1 ∨ i = 2) : 0 < (c.coord i).linear v := by
    have he (k : Fin 3) : (c.coord i).linear (c k - c 0) =
        c.coord i (c k) - c.coord i (c 0) := (c.coord i).linearMap_vsub _ _
    dsimp only [v]
    rw [map_add, he 1, he 2]
    rcases hi with rfl | rfl <;> norm_num [AffineBasis.coord_apply, Fin.ext_iff]
  exact wedge_restriction_support_eventuallyEq M (c.coord 1) (c.coord 2)
    h1 h2 (hv 1 (Or.inl rfl)) (hv 2 (Or.inr rfl)) hq

theorem convexSector_complement_restriction_support_eventuallyEq
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : M.IsMonochromatic (c.coord 1)) (h2 : M.IsMonochromatic (c.coord 2))
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support) :
    (M.restrictTriangles (fun t => ¬M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})).toPlaneComplex.support =ᶠ[𝓝 q]
        {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  let N := M.restrictTriangles (fun t => ¬M.triangleCarrier t ⊆
    {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
  have hsurj (i : Fin 3) (hi : i ≠ 0) : Function.Surjective (c.coord i) := by
    intro r
    exact ⟨AffineMap.lineMap (c 0) (c i) r, by
      simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hi]⟩
  have hcover (i : Fin 3) (hi : i = 1 ∨ i = 2) (hmono : M.IsMonochromatic (c.coord i))
      {z : Plane} (hz : z ∈ interior M.toPlaneComplex.support) (hzi : c.coord i z ≤ 0) :
      z ∈ N.toPlaneComplex.support := by
    have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    have hmneg : M.IsMonochromatic (-c.coord i) := by
      apply TriangleMesh.IsMonochromatic.of_neg
      simpa only [neg_neg] using hmono
    have hsneg : Function.Surjective (-c.coord i) := by
      intro r
      obtain ⟨w, hw⟩ := hsurj i hi0 (-r)
      exact ⟨w, by change -(c.coord i w) = r; rw [hw, neg_neg]⟩
    have hmem := mem_halfspace_restriction_of_mem_interior M (-c.coord i) hsneg hmneg hz
      (show 0 ≤ (-c.coord i) z from neg_nonneg.mpr hzi)
    rw [TriangleMesh.toPlaneComplex_support] at hmem ⊢
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hmem
    obtain ⟨htM, htneg⟩ := (M.mem_restrictTriangles_triangles _).mp ht
    refine mem_iUnion₂.mpr ⟨t, (M.mem_restrictTriangles_triangles _).mpr ⟨htM, ?_⟩, hzt⟩
    intro htpos
    have heq : c.coord i = 0 := by
      apply AffineMap.ext_on (meshTriangleBasis M ⟨t, htM⟩).tot
      rintro w ⟨k, rfl⟩
      have hk : meshTriangleBasis M ⟨t, htM⟩ k ∈ M.triangleCarrier t := by
        rw [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis M ⟨t, htM⟩]
        exact subset_convexHull ℝ _ (mem_range_self k)
      apply le_antisymm (by simpa using htneg hk)
      rcases hi with rfl | rfl
      · exact (htpos hk).1
      · exact (htpos hk).2
    have hh := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (c i)) heq
    simp at hh
  filter_upwards [isOpen_interior.mem_nhds hq] with z hz
  apply propext
  change z ∈ N.toPlaneComplex.support ↔ c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0
  constructor
  · intro hzn
    rw [TriangleMesh.toPlaneComplex_support] at hzn
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzn
    obtain ⟨htM, htneg⟩ := (M.mem_restrictTriangles_triangles _).mp ht
    rcases h1.triangleCarrier_halfspace M ⟨t, htM⟩ with hp1 | hn1
    · rcases h2.triangleCarrier_halfspace M ⟨t, htM⟩ with hp2 | hn2
      · exact False.elim (htneg (fun w hw => ⟨hp1 w hw, hp2 w hw⟩))
      · exact Or.inr (hn2 z hzt)
    · exact Or.inl (hn1 z hzt)
  · exact fun h => h.elim (hcover 1 (Or.inl rfl) h1 hz) (hcover 2 (Or.inr rfl) h2 hz)

theorem meshVertexAngleContribution_restrictTriangles_mono
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P Q : Finset M.Vertex → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ t ∈ M.triangles, P t → Q t) (x : S) :
    meshVertexAngleContribution g F (M.restrictTriangles P) x ≤
      meshVertexAngleContribution g F (M.restrictTriangles Q) x := by
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum,
    meshVertexAngleContribution_restrictTriangles_eq_sum]
  apply Finset.sum_le_sum
  intro t _
  have hn : 0 ≤ ∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0 := by
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact Real.arccos_nonneg _
    · rfl
  by_cases hp : P t.1
  · simp only [hp, hPQ t.1 t.2 hp, if_true, le_refl]
  · simp only [hp, if_false]
    split_ifs <;> first | exact hn | exact le_refl 0

theorem single_refineByLines_convexSector_vertex_fan_of_monochromatic
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (h1 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (a : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex) (hau : a ∈ u.1)
    (haint : ((TriangleMesh.single b b.ind).refineByLines lines).position a ∈
      interior (convexHull ℝ (range b)))
    (ha0 : ((TriangleMesh.single b b.ind).refineByLines lines).position a = c 0) :
    let M := (TriangleMesh.single b b.ind).refineByLines lines
    meshVertexAngleContribution g F (M.restrictTriangles (fun t => M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})) (F (M.position a)) =
      g.cornerAngle (F (M.position a))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆
    {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
  have hM : M.toPlaneComplex.support ⊆ F.source := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hb
  have hai : M.position a ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  have ha : M.position a ∈ F.source := hM (interior_subset hai)
  have hal : c.coord 1 (M.position a) = 0 := by rw [ha0]; simp
  have ham : c.coord 2 (M.position a) = 0 := by rw [ha0]; simp
  let v := (c 1 - c 0) + (c 2 - c 0)
  have hv (i : Fin 3) (hi : i = 1 ∨ i = 2) : 0 < (c.coord i).linear v := by
    have he (k : Fin 3) : (c.coord i).linear (c k - c 0) =
        c.coord i (c k) - c.coord i (c 0) := (c.coord i).linearMap_vsub _ _
    dsimp only [v]
    rw [map_add, he 1, he 2]
    rcases hi with rfl | rfl <;> norm_num [AffineBasis.coord_apply, Fin.ext_iff]
  have hmem := mem_wedge_restriction_of_mem_interior M (c.coord 1) (c.coord 2)
    h1 h2 (hv 1 (Or.inl rfl)) (hv 2 (Or.inr rfl)) hai hal.ge ham.ge
  rw [TriangleMesh.toPlaneComplex_support] at hmem
  obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp hmem
  let tM : M.Triangle := ⟨t, ((M.mem_restrictTriangles_triangles _).mp ht).1⟩
  have hatM : a ∈ t := mesh_usedVertex_mem_triangle_of_mem_hull M tM u hau
    (by rw [range_meshTriangleBasis]; exact hat)
  have hpos := meshVertexAngleContribution_pos_of_used_vertex g F N a ⟨t, ht⟩ hatM
    hF hFi ((restrictTriangles_support_subset M _).trans hM)
  have hsurj : Function.Surjective (c.coord 1) := by
    intro r
    exact ⟨AffineMap.lineMap (c 0) (c 1) r, by
      simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]⟩
  have hhalf := single_refineByLines_halfspace_vertex_fan_of_monochromatic
    g F b lines (c.coord 1) hsurj h1 hF hFi hb u a hau haint hal
  have hle : meshVertexAngleContribution g F N (F (M.position a)) ≤ Real.pi := by
    rw [← hhalf]
    exact meshVertexAngleContribution_restrictTriangles_mono g F M _ _
      (fun _ _ h _ hz => (h hz).1) _
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let p := F (M.position a)
  let : Fact (Module.finrank ℝ (TangentSpace (𝓡 2) p) = 2) := ⟨finrank_euclideanSpace_fin⟩
  let o : Orientation ℝ (TangentSpace (𝓡 2) p) (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let L : Plane →ₗ[ℝ] TangentSpace (𝓡 2) p :=
    (mfderiv (𝓡 2) (𝓡 2) F (M.position a)).toLinearMap
  have hL : Function.Injective L :=
    (show F.MDifferentiable (𝓡 2) (𝓡 2) from
      ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩).mfderiv_injective ha
  have heq := meshVertexAngleContribution_eq_sum_linearCorner g F N a hF
    ((restrictTriangles_support_subset M _).trans hM) ha
  change meshVertexAngleContribution g F N (F (M.position a)) =
    ∑ t : N.Triangle, meshLinearCorner N L a t at heq
  have hcoe := convexSector_sum_linearCorner_coe_eq_zero_or_angle M c h1 h2 o L hL a hai ha0
  change ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) = 0 ∨
    ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) =
      (InnerProductGeometry.angle (L (c 1 - c 0)) (L (c 2 - c 0)) : Real.Angle) at hcoe
  rw [← heq] at hcoe
  change 0 < meshVertexAngleContribution g F N (F (M.position a)) at hpos
  have hrepr := Real.Angle.toReal_coe_eq_self_iff.mpr
    (show -Real.pi < meshVertexAngleContribution g F N (F (M.position a)) ∧
      meshVertexAngleContribution g F N (F (M.position a)) ≤ Real.pi from
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans hpos, hle⟩)
  have hθ := affineBasis_linear_angle_mem_Ioo L hL c
  have hθrepr := Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨(neg_lt_zero.mpr Real.pi_pos).trans hθ.1, hθ.2.le⟩
  change meshVertexAngleContribution g F N (F (M.position a)) = _
  rw [cornerAngle_eq_innerProduct_angle]
  rcases hcoe with hz | he
  · have h := congrArg Real.Angle.toReal hz
    rw [hrepr, Real.Angle.toReal_zero] at h
    exact False.elim (hpos.ne' h)
  · have h := congrArg Real.Angle.toReal he
    rw [hrepr, hθrepr] at h
    exact h

theorem single_refineByLines_restrict_convexSector_vertex_fan_of_support_eventuallyEq
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (h1 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (a : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex) (hau : a ∈ u.1)
    (haint : ((TriangleMesh.single b b.ind).refineByLines lines).position a ∈
      interior (convexHull ℝ (range b)))
    (ha0 : ((TriangleMesh.single b b.ind).refineByLines lines).position a = c 0)
    (hP : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 (((TriangleMesh.single b b.ind).refineByLines lines).position a)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    let M := (TriangleMesh.single b b.ind).refineByLines lines
    meshVertexAngleContribution g F (M.restrictTriangles P) (F (M.position a)) =
      g.cornerAngle (F (M.position a))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  have hM : M.toPlaneComplex.support ⊆ F.source := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hb
  have hai : M.position a ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  have hsel := convexSector_restriction_support_eventuallyEq M c h1 h2 hai
  have hglue := meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    g F M P (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    hM (hM (interior_subset hai)) (hP.trans hsel.symm)
  change meshVertexAngleContribution g F (M.restrictTriangles P) (F (M.position a)) = _
  rw [hglue]
  exact single_refineByLines_convexSector_vertex_fan_of_monochromatic
    g F b c lines h1 h2 hF hFi hb u a hau haint ha0

theorem single_refineByLines_restrict_convexSector_vertex_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (h1 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (a : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hau : a ∈ u.1)
    (haint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a ∈
      interior (convexHull ℝ (range b)))
    (ha0 : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a = c 0)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    let M := ((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P
    meshVertexAngleContribution g F M (F (M.position a)) =
      g.cornerAngle (F (M.position a))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  let q := (M.restrictTriangles P).position a
  have hq : q ∈ F.source := by
    apply hsource
    apply meshTriangleBasis_subset_support (M.restrictTriangles P) u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨a, hau, rfl⟩
  let G := coordinateTangentMetric g F hF hFi q hq
  have hfan := single_refineByLines_restrict_convexSector_vertex_fan_of_support_eventuallyEq
    G (OpenPartialHomeomorph.refl Plane) b c lines P h1 h2 contMDiffOn_id contMDiffOn_id
    (by simp) (restrictTrianglesTriangleEquiv M P u).1 a hau haint ha0 hlocal
  change meshVertexAngleContribution g F (M.restrictTriangles P) (F q) = _
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
    (M.restrictTriangles P) q = _ at hfan
  rw [hfan]
  change G.cornerAngle q ((mfderiv (𝓡 2) (𝓡 2) id q) (c 1 - c 0))
    ((mfderiv (𝓡 2) (𝓡 2) id q) (c 2 - c 0)) = _
  rw [mfderiv_id]
  simp only [G, RiemannianMetric.cornerAngle,
    coordinateTangentMetric_inner, map_smul, smul_apply]
  rfl

theorem single_refineByLines_convexSector_complement_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (h1 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (a : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex) (hau : a ∈ u.1)
    (haint : ((TriangleMesh.single b b.ind).refineByLines lines).position a ∈
      interior (convexHull ℝ (range b)))
    (ha0 : ((TriangleMesh.single b b.ind).refineByLines lines).position a = c 0) :
    let M := (TriangleMesh.single b b.ind).refineByLines lines
    meshVertexAngleContribution g F (M.restrictTriangles (fun t => ¬M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})) (F (M.position a)) = 2 * Real.pi -
      g.cornerAngle (F (M.position a))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  have hai : M.position a ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  have hsum := meshVertexAngleContribution_restrictTriangles_add_compl g F M
    (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    (F (M.position a))
  have hw := single_refineByLines_convexSector_vertex_fan_of_monochromatic
    g F b c lines h1 h2 hF hFi hb u a hau haint ha0
  have hall := single_refineByLines_interior_vertex_fan g F b lines hF hFi hb u a hau hai
  change meshVertexAngleContribution g F
    (M.restrictTriangles (fun t => ¬M.triangleCarrier t ⊆
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})) (F (M.position a)) = _
  rw [hw, hall] at hsum
  linarith

theorem single_refineByLines_restrict_reflexSector_vertex_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (h1 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (a : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hau : a ∈ u.1)
    (haint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a ∈
      interior (convexHull ℝ (range b)))
    (ha0 : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a = c 0)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)]
        {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    let M := ((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P
    meshVertexAngleContribution g F M (F (M.position a)) = 2 * Real.pi -
      g.cornerAngle (F (M.position a))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (M.position a)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  let q := (M.restrictTriangles P).position a
  have hq : q ∈ F.source := by
    apply hsource
    apply meshTriangleBasis_subset_support (M.restrictTriangles P) u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨a, hau, rfl⟩
  have hqi : q ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  let G := coordinateTangentMetric g F hF hFi q hq
  have hsel := convexSector_complement_restriction_support_eventuallyEq M c h1 h2 hqi
  have hglue := meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    G (OpenPartialHomeomorph.refl Plane) M P
    (fun t => ¬M.triangleCarrier t ⊆ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
    (by simp) (q := q) (by simp) (by
      convert! hlocal.trans hsel.symm using 1
      congr 3)
  have hfan := single_refineByLines_convexSector_complement_vertex_fan
    G (OpenPartialHomeomorph.refl Plane) b c lines h1 h2 contMDiffOn_id contMDiffOn_id
    (by simp) (restrictTrianglesTriangleEquiv M P u).1 a hau haint ha0
  change meshVertexAngleContribution g F (M.restrictTriangles P) (F q) = _
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  have heq : meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
      (M.restrictTriangles P) q = 2 * Real.pi - G.cornerAngle q
        ((mfderiv (𝓡 2) (𝓡 2) id q) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) id q) (c 2 - c 0)) := by
    apply hglue.trans
    convert! hfan using 1
    congr 2
  rw [heq]
  congr 1
  rw [mfderiv_id]
  simp only [G, RiemannianMetric.cornerAngle, coordinateTangentMetric_inner, map_smul, smul_apply]
  rfl

theorem meshVertexAngleContribution_restrictTriangles_union_add_inter
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P Q : Finset M.Vertex → Prop)
    [DecidablePred P] [DecidablePred Q] (x : S) :
    meshVertexAngleContribution g F (M.restrictTriangles (fun t => P t ∨ Q t)) x +
      meshVertexAngleContribution g F (M.restrictTriangles (fun t => P t ∧ Q t)) x =
        meshVertexAngleContribution g F (M.restrictTriangles P) x +
          meshVertexAngleContribution g F (M.restrictTriangles Q) x := by
  simp_rw [meshVertexAngleContribution_restrictTriangles_eq_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hp : P t.1 <;> by_cases hq : Q t.1 <;> simp [hp, hq]

end MetricSector

end PoincareConjecture.Topology.Surface

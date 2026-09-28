import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.StraightBoundaryFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CornerBounds
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface



theorem mesh_edge_exists_other_parent_of_interior
    (M : TriangleMesh) (t : M.Triangle) {a b : M.Vertex}
    (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) {q : Plane}
    (hq : q ∈ openSegment ℝ (M.position a) (M.position b))
    (hqint : q ∈ interior M.toPlaneComplex.support) :
    ∃ u : M.Triangle, u ≠ t ∧ a ∈ u.1 ∧ b ∈ u.1 := by
  by_contra hnone
  have havoid : ∀ u : M.Triangle, u ≠ t →
      q ∉ convexHull ℝ (range (meshTriangleBasis M u)) := by
    intro u hut hqu
    have hends := mesh_edge_endpoints_mem_of_openSegment_mem_hull M t u ha hb hab hq hqu
    exact hnone ⟨u, hut, hends⟩
  let A : Set Plane := ⋃ u : M.Triangle, ⋃ (_ : u ≠ t),
    convexHull ℝ (range (meshTriangleBasis M u))
  have hclosed : IsClosed A := isClosed_iUnion_of_finite fun u =>
    isClosed_iUnion_of_finite fun (_ : u ≠ t) => (finite_range _).isClosed_convexHull ℝ
  have hqA : q ∉ A := by
    simp only [A, mem_iUnion]
    rintro ⟨u, hut, hqu⟩
    exact havoid u hut hqu
  have hnhds : M.toPlaneComplex.support ∩ Aᶜ ∈ 𝓝 q :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp hqint)
      (hclosed.isOpen_compl.mem_nhds hqA)
  have hsub : M.toPlaneComplex.support ∩ Aᶜ ⊆
      convexHull ℝ (range (meshTriangleBasis M t)) := by
    rintro z ⟨hz, hzA⟩
    rw [← meshTriangleBasis_sources_cover] at hz
    obtain ⟨u, hzu⟩ := mem_iUnion.mp hz
    by_cases hut : u = t
    · exact hut ▸ hzu
    · exact False.elim (hzA (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hut, hzu⟩⟩))
  have hint : q ∈ interior (convexHull ℝ (range (meshTriangleBasis M t))) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnhds hsub)
  obtain ⟨c, hc0, hc1, hcrange⟩ := exists_meshTriangleBasis_with_edge M t ha hb hab
  rw [← hcrange, c.interior_convexHull] at hint
  rw [openSegment_eq_image_lineMap] at hq
  obtain ⟨r, _, rfl⟩ := hq
  have h := hint 2
  norm_num [← hc0, ← hc1, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    AffineBasis.coord_apply, Fin.ext_iff] at h



theorem halfspace_restriction_edge_exists_other_parent
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (t : (M.restrictTriangles
      (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})).Triangle)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) (hbl : 0 < l (M.position b)) :
    ∃ u : (M.restrictTriangles
      (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})).Triangle,
      u ≠ t ∧ a ∈ u.1 ∧ b ∈ u.1 := by
  let N := M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})
  let path : ℝ → Plane := AffineMap.lineMap (M.position a) (M.position b)
  have hp : Continuous path := by
    simp only [path]
    fun_prop
  have hint : ∀ᶠ r in 𝓝 (0 : ℝ), path r ∈ interior M.toPlaneComplex.support :=
    hp.continuousAt.eventually (isOpen_interior.mem_nhds
      (by simpa only [path, AffineMap.lineMap_apply_zero] using haint))
  have hlt : ∀ᶠ r in 𝓝 (0 : ℝ), r < 1 := Iio_mem_nhds (by norm_num)
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < r ∧ r < 1 ∧ path r ∈ interior M.toPlaneComplex.support := by
    filter_upwards [hint.filter_mono nhdsWithin_le_nhds,
      hlt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hlt hpos
    exact ⟨hpos, hlt, hr⟩
  obtain ⟨r, hrpos, hrlt, hrint⟩ := hnear.exists
  have hrl : 0 < l (path r) := by
    simp only [path, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hal,
      mul_zero, zero_add]
    exact mul_pos hrpos hbl
  have hN : path r ∈ interior N.toPlaneComplex.support := by
    apply (isOpen_interior.inter (isOpen_Ioi.preimage l.continuous_of_finiteDimensional)).subset_interior_iff.mpr
      (show interior M.toPlaneComplex.support ∩ l ⁻¹' Ioi (0 : ℝ) ⊆
        N.toPlaneComplex.support from fun z hz =>
          mem_halfspace_restriction_of_mem_interior M l hl hmono hz.1 hz.2.le)
    exact ⟨hrint, hrl⟩
  exact mesh_edge_exists_other_parent_of_interior N t ha hb hab
    (by rw [openSegment_eq_image_lineMap]; exact ⟨r, ⟨hrpos, hrlt⟩, rfl⟩) hN

theorem affineBasis_vsub_zero_eq (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    z - b 0 = b.coord 1 z • (b 1 - b 0) + b.coord 2 z • (b 2 - b 0) := by
  have hs := b.sum_coord_apply_eq_one z
  have hz := b.linear_combination_coord_eq_self z
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs hz
  change b.coord 0 z + (b.coord 1 z + b.coord 2 z) = 1 at hs
  change b.coord 0 z • b 0 + (b.coord 1 z • b 1 + b.coord 2 z • b 2) = z at hz
  nth_rw 1 [← hz]
  have h0 : b.coord 0 z = 1 - b.coord 1 z - b.coord 2 z := by linarith
  rw [h0]
  module

section OrientedAngles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]



theorem angle_coe_eq_sign_smul_oangle
    (o : Orientation ℝ V (Fin 2)) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hangle : InnerProductGeometry.angle x y ∈ Ioo 0 Real.pi) :
    (InnerProductGeometry.angle x y : Real.Angle) =
      ((o.oangle x y).sign : ℤ) • o.oangle x y := by
  rcases SignType.trichotomy (o.oangle x y).sign with hs | hs | hs
  · rw [hs, SignType.coe_neg_one, neg_one_zsmul,
      o.oangle_eq_neg_angle_of_sign_eq_neg_one hs, neg_neg]
  · rcases o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hs with
      h | h | h | h
    · exact False.elim (hx h)
    · exact False.elim (hy h)
    · exact False.elim (hangle.1.ne' h)
    · exact False.elim (hangle.2.ne h)
  · rw [hs, SignType.coe_one, one_zsmul, o.oangle_eq_angle_of_sign_eq_one hs]



theorem affineTriangle_shared_edge_oangle_sign_neg
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hdisjoint : Disjoint (interior (convexHull ℝ (range b)))
      (interior (convexHull ℝ (range c)))) :
    (o.oangle (L (c 1 - c 0)) (L (c 2 - c 0))).sign =
      -(o.oangle (L (b 1 - b 0)) (L (b 2 - b 0))).sign := by
  have hneg := affineTriangle_shared_edge_coord_neg b c h0 h1 hdisjoint
  rw [← h0, ← h1, affineBasis_vsub_zero_eq b (c 2), map_add, map_smul, map_smul,
    o.oangle_sign_smul_add_smul_right]
  simp [hneg]

end OrientedAngles


def meshEdgeBasis (M : TriangleMesh) (t : M.Triangle)
    (a b : M.Vertex) (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) :
    AffineBasis (Fin 3) ℝ Plane :=
  Classical.choose (exists_meshTriangleBasis_with_edge M t ha hb hab)

theorem meshEdgeBasis_zero (M : TriangleMesh) (t : M.Triangle)
    (a b : M.Vertex) (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) :
    meshEdgeBasis M t a b ha hb hab 0 = M.position a :=
  (Classical.choose_spec (exists_meshTriangleBasis_with_edge M t ha hb hab)).1

theorem meshEdgeBasis_one (M : TriangleMesh) (t : M.Triangle)
    (a b : M.Vertex) (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) :
    meshEdgeBasis M t a b ha hb hab 1 = M.position b :=
  (Classical.choose_spec (exists_meshTriangleBasis_with_edge M t ha hb hab)).2.1

theorem range_meshEdgeBasis (M : TriangleMesh) (t : M.Triangle)
    (a b : M.Vertex) (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) :
    range (meshEdgeBasis M t a b ha hb hab) = range (meshTriangleBasis M t) :=
  (Classical.choose_spec (exists_meshTriangleBasis_with_edge M t ha hb hab)).2.2

private theorem affineBasis_third_eq_of_range_eq
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hr : range b = range c) : b 2 = c 2 := by
  have hm : b 2 ∈ range c := hr ▸ mem_range_self (2 : Fin 3)
  obtain ⟨i, hi⟩ := hm
  fin_cases i
  · have := b.ind.injective (h0.trans hi)
    exact False.elim ((by decide : (0 : Fin 3) ≠ 2) this)
  · have := b.ind.injective (h1.trans hi)
    exact False.elim ((by decide : (1 : Fin 3) ≠ 2) this)
  · exact hi.symm

theorem meshEdgeBasis_two_eq_of_range_eq
    (M : TriangleMesh) (t : M.Triangle)
    (a b : M.Vertex) (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = M.position a)
    (hc1 : c 1 = M.position b) (hr : range c = range (meshTriangleBasis M t)) :
    meshEdgeBasis M t a b ha hb hab 2 = c 2 :=
  affineBasis_third_eq_of_range_eq _ _
    ((meshEdgeBasis_zero M t a b ha hb hab).trans hc0.symm)
    ((meshEdgeBasis_one M t a b ha hb hab).trans hc1.symm)
    ((range_meshEdgeBasis M t a b ha hb hab).trans hr.symm)

private theorem sum_mesh_vertex_eq_sum_ordered {A : Type*} [AddCommMonoid A]
    (M : TriangleMesh) (t : M.Triangle) (f : M.Vertex → A)
    (hf : ∀ v ∉ t.1, f v = 0) :
    ∑ v : M.Vertex, f v = ∑ i : Fin 3, f (M.orderedVertex t i) := by
  rw [← (M.triangleEquiv t).sum_comp (fun i => f (M.orderedVertex t i))]
  simp only [TriangleMesh.orderedVertex, Equiv.symm_apply_apply]
  change (∑ v : M.Vertex, f v) = ∑ v ∈ t.1.attach, f v.1
  rw [Finset.sum_attach]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hf v hv)).symm

def meshVertexBasis (M : TriangleMesh) (t : M.Triangle) (a : M.Vertex)
    (ha : a ∈ t.1) : AffineBasis (Fin 3) ℝ Plane :=
  let h := Finset.exists_mem_ne (show 1 < t.1.card by rw [M.card_triangle t.1 t.2]; decide) a
  meshEdgeBasis M t a (Classical.choose h) ha (Classical.choose_spec h).1
    (Classical.choose_spec h).2.symm

theorem meshVertexBasis_zero (M : TriangleMesh) (t : M.Triangle) (a : M.Vertex)
    (ha : a ∈ t.1) : meshVertexBasis M t a ha 0 = M.position a := by
  unfold meshVertexBasis
  exact meshEdgeBasis_zero _ _ _ _ _ _ _

theorem range_meshVertexBasis (M : TriangleMesh) (t : M.Triangle) (a : M.Vertex)
    (ha : a ∈ t.1) : range (meshVertexBasis M t a ha) = range (meshTriangleBasis M t) := by
  unfold meshVertexBasis
  exact range_meshEdgeBasis _ _ _ _ _ _ _

section EdgeSigns

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

private theorem affineBasis_range_reindex (b : AffineBasis (Fin 3) ℝ Plane)
    (e : Equiv.Perm (Fin 3)) : range (b.reindex e) = range b := by
  simp only [AffineBasis.coe_reindex, range_comp, Equiv.range_eq_univ, image_univ]

def meshLinearCorner (M : TriangleMesh) (L : Plane →ₗ[ℝ] V)
    (a : M.Vertex) (t : M.Triangle) : ℝ :=
  if ha : a ∈ t.1 then
    let b := meshVertexBasis M t a ha
    InnerProductGeometry.angle (L (b 1 - b 0)) (L (b 2 - b 0))
  else 0

omit [Fact (Module.finrank ℝ V = 2)] in
theorem affineBasis_linear_angle_mem_Ioo (L : Plane →ₗ[ℝ] V)
    (hL : Function.Injective L) (b : AffineBasis (Fin 3) ℝ Plane) :
    InnerProductGeometry.angle (L (b 1 - b 0)) (L (b 2 - b 0)) ∈ Ioo 0 Real.pi := by
  have hnot (c : ℝ) : L (b 2 - b 0) ≠ c • L (b 1 - b 0) := by
    intro h
    have heq : b 2 - b 0 = c • (b 1 - b 0) := hL (h.trans (map_smul L c _).symm)
    have hcoord := congrArg (b.coord 2).linear heq
    have hval (i : Fin 3) : (b.coord 2).linear (b i - b 0) =
        b.coord 2 (b i) - b.coord 2 (b 0) := (b.coord 2).linearMap_vsub _ _
    rw [map_smul, hval 2, hval 1] at hcoord
    norm_num [AffineBasis.coord_apply, Fin.ext_iff] at hcoord
  constructor
  · apply lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _)
    intro h
    obtain ⟨_, c, _, hc⟩ := InnerProductGeometry.angle_eq_zero_iff.mp h.symm
    exact hnot c hc
  · apply lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _)
    intro h
    obtain ⟨_, c, _, hc⟩ := InnerProductGeometry.angle_eq_pi_iff.mp h
    exact hnot c hc

omit [Fact (Module.finrank ℝ V = 2)] in
theorem meshLinearCorner_nonneg (M : TriangleMesh) (L : Plane →ₗ[ℝ] V)
    (a : M.Vertex) (t : M.Triangle) : 0 ≤ meshLinearCorner M L a t := by
  unfold meshLinearCorner
  split_ifs
  · exact InnerProductGeometry.angle_nonneg _ _
  · rfl

omit [Fact (Module.finrank ℝ V = 2)] in
theorem meshLinearCorner_pos (M : TriangleMesh) (L : Plane →ₗ[ℝ] V)
    (hL : Function.Injective L) (a : M.Vertex) (t : M.Triangle) (ha : a ∈ t.1) :
    0 < meshLinearCorner M L a t := by
  rw [meshLinearCorner, dif_pos ha]
  exact (affineBasis_linear_angle_mem_Ioo L hL _).1



def meshEdgeAngleSign (M : TriangleMesh) (o : Orientation ℝ V (Fin 2))
    (L : Plane →ₗ[ℝ] V) (a b : M.Vertex) (t : M.Triangle) : ℤ :=
  if h : a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b then
    ((o.oangle (L (M.position b - M.position a))
      (L (meshEdgeBasis M t a b h.1 h.2.1 h.2.2 2 - M.position a))).sign : ℤ)
  else 0


theorem meshEdgeAngleSign_neg_of_distinct_parents
    (M : TriangleMesh) (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (t u : M.Triangle) (htu : t ≠ u) {a b : M.Vertex} (hab : a ≠ b)
    (hat : a ∈ t.1) (hbt : b ∈ t.1) (hau : a ∈ u.1) (hbu : b ∈ u.1) :
    meshEdgeAngleSign M o L a b u = -meshEdgeAngleSign M o L a b t := by
  unfold meshEdgeAngleSign
  rw [dif_pos (show a ∈ u.1 ∧ b ∈ u.1 ∧ a ≠ b from ⟨hau, hbu, hab⟩),
    dif_pos (show a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b from ⟨hat, hbt, hab⟩)]
  have hs := affineTriangle_shared_edge_oangle_sign_neg o L
    (meshEdgeBasis M t a b hat hbt hab) (meshEdgeBasis M u a b hau hbu hab)
    (by rw [meshEdgeBasis_zero, meshEdgeBasis_zero])
    (by rw [meshEdgeBasis_one, meshEdgeBasis_one]) (by
      rw [range_meshEdgeBasis, range_meshEdgeBasis]
      exact mesh_common_edge_disjoint_interiors M t u htu hab hat hbt hau hbu)
  rw [meshEdgeBasis_zero, meshEdgeBasis_zero, meshEdgeBasis_one, meshEdgeBasis_one] at hs
  simpa only [SignType.coe_neg] using congrArg (fun s : SignType => (s : ℤ)) hs

theorem meshEdgeAngleSign_eq_basis
    (M : TriangleMesh) (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (t : M.Triangle) (a b : M.Vertex) (hat : a ∈ t.1) (hbt : b ∈ t.1) (hab : a ≠ b)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = M.position a)
    (hc1 : c 1 = M.position b) (hr : range c = range (meshTriangleBasis M t)) :
    meshEdgeAngleSign M o L a b t =
      ((o.oangle (L (c 1 - c 0)) (L (c 2 - c 0))).sign : ℤ) := by
  unfold meshEdgeAngleSign
  rw [dif_pos (show a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b from ⟨hat, hbt, hab⟩),
    meshEdgeBasis_two_eq_of_range_eq M t a b hat hbt hab c hc0 hc1 hr, hc0, hc1]



theorem sum_meshEdgeAngleSign_smul_eq_corner_difference
    {A : Type*} [AddCommGroup A]
    (M : TriangleMesh) (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (t : M.Triangle) (a b c : M.Vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (d : AffineBasis (Fin 3) ℝ Plane)
    (hd0 : d 0 = M.position a) (hd1 : d 1 = M.position b) (hd2 : d 2 = M.position c)
    (hr : range d = range (meshTriangleBasis M t)) (φ : M.Vertex → A) :
    (∑ v : M.Vertex, meshEdgeAngleSign M o L a v t • φ v) =
      ((o.oangle (L (d 1 - d 0)) (L (d 2 - d 0))).sign : ℤ) • (φ b - φ c) := by
  have ht : t.1 = {a, b, c} := by
    ext v
    have hv : v ∈ t.1 ↔ M.position v ∈ range d := by
      rw [hr, range_meshTriangleBasis]
      exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨w, hw, heq⟩ => M.position_injective heq ▸ hw⟩
    rw [hv]
    simp only [Finset.mem_insert, Finset.mem_singleton, mem_range]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (M.position_injective (hd0.symm.trans hi).symm)
      · exact Or.inr (Or.inl (M.position_injective (hd1.symm.trans hi).symm))
      · exact Or.inr (Or.inr (M.position_injective (hd2.symm.trans hi).symm))
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, hd0⟩
      · exact ⟨1, hd1⟩
      · exact ⟨2, hd2⟩
  have hat : a ∈ t.1 := by rw [ht]; simp
  have hbt : b ∈ t.1 := by rw [ht]; simp
  have hct : c ∈ t.1 := by rw [ht]; simp
  have ha : meshEdgeAngleSign M o L a a t = 0 := by simp [meshEdgeAngleSign]
  have hb := meshEdgeAngleSign_eq_basis M o L t a b hat hbt hab d hd0 hd1 hr
  let d' := d.reindex (Equiv.swap (1 : Fin 3) 2)
  have hc := meshEdgeAngleSign_eq_basis M o L t a c hat hct hac d'
    (by simpa [d', AffineBasis.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff] using hd0)
    (by simpa [d', AffineBasis.reindex_apply] using hd2)
    ((affineBasis_range_reindex d _).trans hr)
  have hd' : d' 2 = d 1 := by simp [d', AffineBasis.reindex_apply]
  have hd'0 : d' 0 = d 0 := by
    simp [d', AffineBasis.reindex_apply, Equiv.swap_apply_def, Fin.ext_iff]
  have hd'1 : d' 1 = d 2 := by simp [d', AffineBasis.reindex_apply]
  rw [hd', hd'0, hd'1, o.oangle_rev, Real.Angle.sign_neg, SignType.coe_neg] at hc
  have hsum : (∑ v : M.Vertex, meshEdgeAngleSign M o L a v t • φ v) =
      ∑ v ∈ ({a, b, c} : Finset M.Vertex), meshEdgeAngleSign M o L a v t • φ v := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro v _ hv
    rw [meshEdgeAngleSign, dif_neg, zero_smul]
    exact fun h => hv (ht ▸ h.2.1)
  rw [hsum, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc,
    ha, hb, hc, zero_smul, zero_add, neg_smul, smul_sub]
  exact (sub_eq_add_neg _ _).symm

theorem meshLinearCorner_coe_eq_neg_sum_edge_potential
    (M : TriangleMesh) (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    (hL : Function.Injective L) (a : M.Vertex) (t : M.Triangle) (r : V) (hr : r ≠ 0) :
    (meshLinearCorner M L a t : Real.Angle) =
      -∑ v : M.Vertex, meshEdgeAngleSign M o L a v t •
        o.oangle r (L (M.position v - M.position a)) := by
  by_cases hat : a ∈ t.1
  · let d := meshVertexBasis M t a hat
    have hd0 : d 0 = M.position a := meshVertexBasis_zero M t a hat
    have hdR : range d = range (meshTriangleBasis M t) := range_meshVertexBasis M t a hat
    obtain ⟨b, hb, hbd⟩ : d 1 ∈ M.position '' (t.1 : Set M.Vertex) := by
      rw [← range_meshTriangleBasis, ← hdR]
      exact mem_range_self 1
    obtain ⟨c, hc, hcd⟩ : d 2 ∈ M.position '' (t.1 : Set M.Vertex) := by
      rw [← range_meshTriangleBasis, ← hdR]
      exact mem_range_self 2
    have hab : a ≠ b := by
      intro h
      have := d.ind.injective (hd0.trans ((congrArg M.position h).trans hbd))
      exact (by decide : (0 : Fin 3) ≠ 1) this
    have hac : a ≠ c := by
      intro h
      have := d.ind.injective (hd0.trans ((congrArg M.position h).trans hcd))
      exact (by decide : (0 : Fin 3) ≠ 2) this
    have hbc : b ≠ c := by
      intro h
      have := d.ind.injective (hbd.symm.trans ((congrArg M.position h).trans hcd))
      exact (by decide : (1 : Fin 3) ≠ 2) this
    have hx : L (d 1 - d 0) ≠ 0 := by
      intro h
      have heq : d 1 - d 0 = 0 := hL (h.trans (map_zero L).symm)
      exact (by decide : (1 : Fin 3) ≠ 0) (d.ind.injective (sub_eq_zero.mp heq))
    have hy : L (d 2 - d 0) ≠ 0 := by
      intro h
      have heq : d 2 - d 0 = 0 := hL (h.trans (map_zero L).symm)
      exact (by decide : (2 : Fin 3) ≠ 0) (d.ind.injective (sub_eq_zero.mp heq))
    rw [sum_meshEdgeAngleSign_smul_eq_corner_difference M o L t a b c hab hac hbc
      d hd0 hbd.symm hcd.symm hdR]
    rw [← hd0, hbd, hcd, ← smul_neg, neg_sub,
      o.oangle_sub_left hr hx hy]
    rw [meshLinearCorner, dif_pos hat]
    exact angle_coe_eq_sign_smul_oangle o hx hy (affineBasis_linear_angle_mem_Ioo L hL d)
  · rw [meshLinearCorner, dif_neg hat]
    simp [meshEdgeAngleSign, hat]


theorem sum_meshEdgeAngleSign_eq_zero_of_two_parents
    (M : TriangleMesh) (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V)
    {a b : M.Vertex} (hab : a ≠ b)
    (t u : M.Triangle) (htu : t ≠ u)
    (hat : a ∈ t.1) (hbt : b ∈ t.1) (hau : a ∈ u.1) (hbu : b ∈ u.1) :
    ∑ s : M.Triangle, meshEdgeAngleSign M o L a b s = 0 := by
  have hparents : ∀ s : M.Triangle, a ∈ s.1 → b ∈ s.1 → s = t ∨ s = u := by
    intro s has hbs
    by_contra h
    push Not at h
    have hsub : ({t, u, s} : Finset M.Triangle) ⊆
        Finset.univ.filter (fun w : M.Triangle => a ∈ w.1 ∧ b ∈ w.1) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> simp [hat, hbt, hau, hbu, has, hbs]
    have hc := (Finset.card_le_card hsub).trans (mesh_edge_parent_card_le_two M hab)
    simp [htu, h.1.symm, h.2.symm] at hc
  have heq : (∑ s : M.Triangle, meshEdgeAngleSign M o L a b s) =
      ∑ s ∈ ({t, u} : Finset M.Triangle), meshEdgeAngleSign M o L a b s := by
    apply (Finset.sum_subset (Finset.subset_univ ({t, u} : Finset M.Triangle)) ?_).symm
    intro s _ hs
    simp only [meshEdgeAngleSign]
    split_ifs with h
    · exact False.elim (hs (by simpa using hparents s h.1 h.2.1))
    · rfl
  rw [heq, Finset.sum_pair htu,
    meshEdgeAngleSign_neg_of_distinct_parents M o L t u htu hab hat hbt hau hbu,
    add_neg_cancel]




theorem sum_halfspace_meshEdgeAngleSign_smul_eq_zero
    {A : Type*} [AddCommGroup A]
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V) (a : M.Vertex)
    (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) (φ : M.Vertex → A)
    (hφ : ∀ b, l (M.position b) = 0 → φ b = 0) :
    ∑ t : (M.restrictTriangles
      (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})).Triangle,
      ∑ b : M.Vertex, meshEdgeAngleSign
        (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z}))
        o L a b t • φ b = 0 := by
  let N := M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hbl : l (M.position b) = 0
  · simp only [hφ b hbl, smul_zero, Finset.sum_const_zero]
  · by_cases hparents : ∃ t : N.Triangle, a ∈ t.1 ∧ b ∈ t.1 ∧ a ≠ b
    · obtain ⟨t, hat, hbt, hab⟩ := hparents
      have hbpos : 0 < l (M.position b) := by
        apply lt_of_le_of_ne _ (Ne.symm hbl)
        exact ((M.mem_restrictTriangles_triangles _).mp t.2).2
          (subset_convexHull ℝ _ ⟨b, hbt, rfl⟩)
      obtain ⟨u, hut, hau, hbu⟩ := halfspace_restriction_edge_exists_other_parent
        M l hl hmono t hat hbt hab haint hal hbpos
      rw [← Finset.sum_smul, sum_meshEdgeAngleSign_eq_zero_of_two_parents
        N o L hab t u hut.symm hat hbt hau hbu, zero_smul]
    · apply Finset.sum_eq_zero
      intro t _
      rw [meshEdgeAngleSign, dif_neg (fun h => hparents ⟨t, h⟩), zero_smul]

end EdgeSigns



theorem exists_affineLine_direction (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) :
    ∃ w : Plane, w ≠ 0 ∧ l.linear w = 0 ∧
      ∀ v : Plane, l.linear v = 0 → ∃ c : ℝ, v = c • w := by
  have hrange : LinearMap.range l.linear = ⊤ :=
    LinearMap.range_eq_top.mpr (l.linear_surjective_iff.mpr hl)
  have hdim := l.linear.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  have hker : Module.finrank ℝ (LinearMap.ker l.linear) = 1 := by
    simp only [Plane, Module.finrank_self, finrank_euclideanSpace_fin] at hdim
    exact Nat.add_left_cancel (hdim.trans (by norm_num : 2 = 1 + 1))
  obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp (by rw [hker] :
      1 ≤ Module.finrank ℝ (LinearMap.ker l.linear)))
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hker hw hwne
  refine ⟨w, hwne, hw, ?_⟩
  intro v hv
  have hmem : v ∈ Submodule.span ℝ {w} := by rw [← hspan]; exact hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

section Quantization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

private theorem twice_halfspace_angle_sum_coe_eq_zero
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (o : Orientation ℝ V (Fin 2)) (L : Plane →ₗ[ℝ] V) (hL : Function.Injective L)
    (a : M.Vertex) (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) :
    (2 : ℤ) • ((∑ t : (M.restrictTriangles
      (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})).Triangle,
        meshLinearCorner (M.restrictTriangles
          (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) L a t : ℝ) : Real.Angle) = 0 := by
  let N := M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})
  obtain ⟨w, hw, hwl, hspan⟩ := exists_affineLine_direction l hl
  have hLw : L w ≠ 0 := fun h => hw (hL (h.trans (map_zero L).symm))
  let φ : M.Vertex → Real.Angle := fun v =>
    (2 : ℤ) • o.oangle (L w) (L (M.position v - M.position a))
  have hφ : ∀ v, l (M.position v) = 0 → φ v = 0 := by
    intro v hv
    have hdir : l.linear (M.position v - M.position a) = 0 := by
      change l.linear (M.position v -ᵥ M.position a) = 0
      rw [l.linearMap_vsub, hv, hal, vsub_self]
    obtain ⟨c, hc⟩ := hspan _ hdir
    have hs := (o.oangle_eq_zero_or_eq_pi_iff_right_eq_smul
      (x := L w) (y := L (M.position v - M.position a))).mpr
      (Or.inr ⟨c, by rw [hc, map_smul]⟩)
    rcases hs with hs | hs
    · simp only [φ, hs, smul_zero]
    · simp only [φ, hs, Real.Angle.two_zsmul_coe_pi]
  have hcancel := sum_halfspace_meshEdgeAngleSign_smul_eq_zero
    M l hl hmono o L a haint hal φ hφ
  change (2 : ℤ) • ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) = 0
  have hcoe : ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) =
      ∑ t : N.Triangle, (meshLinearCorner N L a t : Real.Angle) :=
    map_sum Real.Angle.coeHom _ _
  rw [hcoe]
  simp_rw [meshLinearCorner_coe_eq_neg_sum_edge_potential N o L hL a _ (L w) hLw]
  rw [Finset.smul_sum]
  simp_rw [smul_neg, Finset.smul_sum, smul_comm (2 : ℤ)]
  rw [Finset.sum_neg_distrib]
  exact neg_eq_zero.mpr hcancel

end Quantization

section Metric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem cornerAngle_eq_innerProduct_angle
    (g : RiemannianMetric 2 S) (p : S) (v w : TangentSpace (𝓡 2) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
    g.cornerAngle p v w = InnerProductGeometry.angle v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold RiemannianMetric.cornerAngle InnerProductGeometry.angle
  change Real.arccos (inner ℝ
    ((Real.sqrt (inner ℝ v v))⁻¹ • v) ((Real.sqrt (inner ℝ w w))⁻¹ • w)) = _
  simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
    real_inner_smul_left, inner_smul_right, mul_inv_rev, div_eq_mul_inv]
  congr 1
  ring

theorem meshVertexAngleContribution_eq_sum_linearCorner
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (a : M.Vertex)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hM : M.toPlaneComplex.support ⊆ F.source) (ha : M.position a ∈ F.source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
    meshVertexAngleContribution g F M (F (M.position a)) =
      ∑ t : M.Triangle, meshLinearCorner M
        (mfderiv (𝓡 2) (𝓡 2) F (M.position a)).toLinearMap a t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold meshVertexAngleContribution
  apply Finset.sum_congr rfl
  intro t _
  by_cases hat : a ∈ t.1
  · let d := meshVertexBasis M t a hat
    have hd0 : d 0 = M.position a := meshVertexBasis_zero M t a hat
    have hdR : range d = range (meshTriangleBasis M t) := range_meshVertexBasis M t a hat
    have hdS : convexHull ℝ (range d) ⊆ F.source := by
      rw [hdR]
      exact (meshTriangleBasis_subset_support M t).trans hM
    rw [coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ d hdR.symm]
    have heq (i : Fin 3) : F (d i) = F (M.position a) ↔ i = 0 := by
      constructor
      · intro h
        exact d.ind.injective ((F.injOn
          (hdS (subset_convexHull ℝ _ (mem_range_self i))) ha h).trans hd0.symm)
      · rintro rfl
        exact congrArg F hd0
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [meshLinearCorner, dif_pos hat]
    change g.cornerAngle (F (d 0)) (coordinateTriangleVelocity F d 0 1)
      (coordinateTriangleVelocity F d 0 2) = _
    rw [coordinateTriangleVelocity_eq_differential F d hF hdS,
      coordinateTriangleVelocity_eq_differential F d hF hdS]
    dsimp only [TangentSpace]
    rw [hd0]
    exact cornerAngle_eq_innerProduct_angle g _ _ _
  · rw [meshLinearCorner, dif_neg hat]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    have hpos := F.injOn (hM (meshTriangleBasis_subset_support M t
      (subset_convexHull ℝ _ (mem_range_self i)))) ha h
    change M.position (M.orderedVertex t i) = M.position a at hpos
    exact hat (M.position_injective hpos ▸ M.orderedVertex_mem t i)



theorem halfspace_meshVertexAngleContribution_mem_pi_multiples
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (a : M.Vertex) (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) :
    ∃ n : ℤ, meshVertexAngleContribution g F
      (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z}))
      (F (M.position a)) = n * Real.pi := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let p := F (M.position a)
  let : Fact (Module.finrank ℝ (TangentSpace (𝓡 2) p) = 2) := ⟨finrank_euclideanSpace_fin⟩
  let o : Orientation ℝ (TangentSpace (𝓡 2) p) (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let L : Plane →ₗ[ℝ] TangentSpace (𝓡 2) p :=
    (mfderiv (𝓡 2) (𝓡 2) F (M.position a)).toLinearMap
  have ha : M.position a ∈ F.source := hM (interior_subset haint)
  have hL : Function.Injective L :=
    (show F.MDifferentiable (𝓡 2) (𝓡 2) from
      ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩).mfderiv_injective ha
  let N := M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})
  have heq := meshVertexAngleContribution_eq_sum_linearCorner g F N a hF
    ((restrictTriangles_support_subset M _).trans hM) ha
  change meshVertexAngleContribution g F N (F (M.position a)) =
    ∑ t : N.Triangle, meshLinearCorner N L a t at heq
  have hquant := twice_halfspace_angle_sum_coe_eq_zero M l hl hmono o L hL a haint hal
  change (2 : ℤ) • ((∑ t : N.Triangle, meshLinearCorner N L a t : ℝ) : Real.Angle) = 0 at hquant
  rw [← heq, ← Real.Angle.coe_zsmul, zsmul_eq_mul, Int.cast_two] at hquant
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hquant
  simp only [zsmul_eq_mul] at hn
  exact ⟨n, by linarith⟩

theorem meshVertexAngleContribution_pos_of_used_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (a : M.Vertex) (u : M.Triangle) (hau : a ∈ u.1)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    0 < meshVertexAngleContribution g F M (F (M.position a)) := by
  have hn (t : M.Triangle) (i : Fin 3) :
      0 ≤ if F (meshTriangleBasis M t i) = F (M.position a) then
        coordinateTriangleAngle g F (meshTriangleBasis M t) i else 0 := by
    split_ifs
    · exact Real.arccos_nonneg _
    · rfl
  unfold meshVertexAngleContribution
  apply Finset.sum_pos' (fun t _ => Finset.sum_nonneg (fun i _ => hn t i))
  refine ⟨u, Finset.mem_univ _, ?_⟩
  obtain ⟨i, hi⟩ : a ∈ range (M.orderedVertex u) := by
    rw [M.range_orderedVertex]
    exact hau
  apply Finset.sum_pos' (fun j _ => hn u j)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  have hpoint : meshTriangleBasis M u i = M.position a := congrArg M.position hi
  rw [hpoint, if_pos rfl]
  exact (coordinateTriangleAngle_mem_Ioo g F _ hF hFi
    ((meshTriangleBasis_subset_support M u).trans hM) i).1

private theorem halfspace_restriction_has_used_vertex
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (a : M.Vertex) (t : M.Triangle) (hat : a ∈ t.1)
    (haint : M.position a ∈ interior M.toPlaneComplex.support)
    (hal : l (M.position a) = 0) :
    ∃ u : (M.restrictTriangles
      (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})).Triangle, a ∈ u.1 := by
  have hmem := mem_halfspace_restriction_of_mem_interior M l hl hmono haint hal.ge
  rw [TriangleMesh.toPlaneComplex_support] at hmem
  obtain ⟨s, hs, has⟩ := mem_iUnion₂.mp hmem
  let u : M.Triangle := ⟨s, ((M.mem_restrictTriangles_triangles _).mp hs).1⟩
  refine ⟨⟨s, hs⟩, mesh_usedVertex_mem_triangle_of_mem_hull M u t hat ?_⟩
  rw [range_meshTriangleBasis]
  exact has

private theorem halfspace_opposite_selection_iff
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l) (t : M.Triangle) :
    (M.triangleCarrier t.1 ⊆ {z | 0 ≤ (-l) z}) ↔
      ¬M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z} := by
  have hnotboth : ¬((M.triangleCarrier t.1 ⊆ {z | 0 ≤ (-l) z}) ∧
      (M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z})) := by
    rintro ⟨hn, hp⟩
    have hzero : l = 0 := by
      apply AffineMap.ext_on (meshTriangleBasis M t).tot
      rintro z ⟨i, rfl⟩
      have hi : meshTriangleBasis M t i ∈ M.triangleCarrier t.1 := by
        rw [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis]
        exact subset_convexHull ℝ _ (mem_range_self i)
      exact le_antisymm (by simpa using hn hi) (hp hi)
    obtain ⟨z, hz⟩ := hl 1
    rw [hzero] at hz
    norm_num at hz
  constructor
  · exact fun hn hp => hnotboth ⟨hn, hp⟩
  · intro hp
    rcases hmono.triangleCarrier_halfspace M t with hpos | hneg
    · exact False.elim (hp hpos)
    · intro z hz
      simpa using hneg z hz

private theorem halfspace_contributions_add_opposite
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l) (x : S) :
    meshVertexAngleContribution g F
      (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) x +
      meshVertexAngleContribution g F
      (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ (-l) z})) x =
        meshVertexAngleContribution g F M x := by
  have h := meshVertexAngleContribution_restrictTriangles_add_compl g F M
    (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z}) x
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum g F M
    (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ (-l) z})]
  simp_rw [halfspace_opposite_selection_iff M l hl hmono]
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum g F M
    (fun s => ¬M.triangleCarrier s ⊆ {z | 0 ≤ l z})] at h
  exact h




theorem single_refineByLines_halfspace_vertex_fan_of_monochromatic
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hmono : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (a : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex)
    (hau : a ∈ u.1)
    (haint : ((TriangleMesh.single b b.ind).refineByLines lines).position a ∈
      interior (convexHull ℝ (range b)))
    (hal : l (((TriangleMesh.single b b.ind).refineByLines lines).position a) = 0) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles
        (fun s => ((TriangleMesh.single b b.ind).refineByLines lines).triangleCarrier s ⊆
          {z | 0 ≤ l z}))
      (F (((TriangleMesh.single b b.ind).refineByLines lines).position a)) = Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  have hmneg : M.IsMonochromatic (-l) := by
    intro t ht
    rcases hmono t ht with h | h
    · exact Or.inr (fun v hv => by simpa using h v hv)
    · exact Or.inl (fun v hv => by simpa using h v hv)
  have hlneg : Function.Surjective (-l) := by
    intro y
    obtain ⟨x, hx⟩ := hl (-y)
    exact ⟨x, by simp [hx]⟩
  have hM : M.toPlaneComplex.support ⊆ F.source := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hb
  have hai : M.position a ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  obtain ⟨up, hup⟩ := halfspace_restriction_has_used_vertex M l hl hmono a u hau hai hal
  obtain ⟨un, hun⟩ := halfspace_restriction_has_used_vertex M (-l) hlneg hmneg a u hau hai
    (by simpa using hal)
  have hp := meshVertexAngleContribution_pos_of_used_vertex g F
    (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) a up hup hF hFi
    ((restrictTriangles_support_subset M _).trans hM)
  have hn := meshVertexAngleContribution_pos_of_used_vertex g F
    (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ (-l) z})) a un hun hF hFi
    ((restrictTriangles_support_subset M _).trans hM)
  have hsum := halfspace_contributions_add_opposite g F M l hl hmono (F (M.position a))
  rw [single_refineByLines_interior_vertex_fan g F b lines hF hFi hb u a hau hai] at hsum
  obtain ⟨n, hnp⟩ := halfspace_meshVertexAngleContribution_mem_pi_multiples
    g F M l hl hmono hF hFi hM a hai hal
  change 0 < meshVertexAngleContribution g F
    (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z}))
    (F (M.position a)) at hp
  change 0 < meshVertexAngleContribution g F
    (M.restrictTriangles (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ (-l) z}))
    (F (M.position a)) at hn
  have hnp0 : (0 : ℝ) < n := (mul_pos_iff_of_pos_right Real.pi_pos).mp (hnp ▸ hp)
  have hnp2 : (n : ℝ) < 2 := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    nlinarith [hnp]
  have hn1 : n = 1 := by
    have h0 : (0 : ℤ) < n := by exact_mod_cast hnp0
    have h2 : n < (2 : ℤ) := by exact_mod_cast hnp2
    omega
  simpa only [hn1, Int.cast_one, one_mul] using hnp



theorem single_refineByLines_halfspace_vertex_fan_of_mem
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) (hmem : l ∈ lines)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines lines).Triangle)
    (a : ((TriangleMesh.single b b.ind).refineByLines lines).Vertex)
    (hau : a ∈ u.1)
    (haint : ((TriangleMesh.single b b.ind).refineByLines lines).position a ∈
      interior (convexHull ℝ (range b)))
    (hal : l (((TriangleMesh.single b b.ind).refineByLines lines).position a) = 0) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles
        (fun s => ((TriangleMesh.single b b.ind).refineByLines lines).triangleCarrier s ⊆
          {z | 0 ≤ l z}))
      (F (((TriangleMesh.single b b.ind).refineByLines lines).position a)) = Real.pi :=
  single_refineByLines_halfspace_vertex_fan_of_monochromatic g F b lines l hl
    ((TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem lines hmem)
    hF hFi hb u a hau haint hal




theorem single_refineByLines_restrict_straight_boundary_fan_of_mem_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) (hmem : l ∈ lines)
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (a : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hau : a ∈ u.1)
    (haint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a ∈
      interior (convexHull ℝ (range b)))
    (hal : l ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a) = 0)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)]
        {z | 0 ≤ l z}) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P)
      (F ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)) =
        Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  let q := (M.restrictTriangles P).position a
  have hq : q ∈ F.source := by
    apply hsource
    apply meshTriangleBasis_subset_support (M.restrictTriangles P) u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨a, hau, rfl⟩
  let G := coordinateTangentMetric g F hF hFi q hq
  have hM : M.IsMonochromatic l :=
    (TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem lines hmem
  have hqint : q ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  have hglue := meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    G (OpenPartialHomeomorph.refl Plane) M P
    (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z}) (by simp) (q := q) (by simp)
    (hlocal.trans (halfspace_restriction_support_eventuallyEq M l hl hM hqint).symm)
  apply hglue.trans
  exact single_refineByLines_halfspace_vertex_fan_of_mem G (OpenPartialHomeomorph.refl Plane)
    b lines l hl hmem contMDiffOn_id contMDiffOn_id (by simp)
    (restrictTrianglesTriangleEquiv M P u).1 a hau haint hal

end Metric

end PoincareConjecture.Topology.Surface

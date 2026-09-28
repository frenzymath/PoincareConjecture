import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.CornerComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.CornerFamilyTransport









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

def cornerVertex (c : Fin 3) : ℝ × ℝ := cornerMap c (0, 0)

theorem cornerVertex_mem (c : Fin 3) : cornerVertex c ∈ vertices := by
  fin_cases c <;> norm_num [cornerVertex, cornerMap, vertices]

theorem range_cornerVertex : range cornerVertex = vertices := by
  apply Subset.antisymm
  · rintro _ ⟨c, rfl⟩
    exact cornerVertex_mem c
  · rintro x (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩
      change cornerMap 1 (0, 0) = (1, 0)
      norm_num only [cornerMap_one, sub_zero]
    · refine ⟨2, ?_⟩
      change cornerMap 2 (0, 0) = (0, 1)
      norm_num only [cornerMap_two, sub_zero]

theorem cornerVertex_injective : Function.Injective cornerVertex := by
  intro c d h
  fin_cases c <;> fin_cases d
  all_goals norm_num [cornerVertex, cornerMap, Prod.mk.injEq] at h
  all_goals rfl

theorem cornerMap_image_vertices (c : Fin 3) : cornerMap c '' vertices = vertices := by
  have hmem (x : ℝ × ℝ) (hx : x ∈ vertices) : cornerMap c x ∈ vertices := by
    rcases hx with rfl | rfl | rfl <;> fin_cases c <;> norm_num [cornerMap, vertices]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hmem x hx
  · intro x hx
    exact ⟨cornerMap c x, hmem x hx, cornerMap_involutive c x⟩

theorem cornerMap_cornerVertex_eq_zero_iff (c d : Fin 3) :
    cornerMap c (cornerVertex d) = (0, 0) ↔ d = c := by
  constructor
  · intro h
    apply cornerVertex_injective
    have he := congrArg (cornerMap c) h
    rw [cornerMap_involutive c (cornerVertex d)] at he
    exact he
  · intro h
    subst d
    exact cornerMap_involutive c (0, 0)

theorem preconnected_corner_vertex_isolated {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {W J : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hproper : W \ {(0, b), (a, 0)} ⊆ base \ frontier base)
    (hJ : IsPreconnected J) (hJsub : J ⊆ base) (hJW : Disjoint J W)
    (hzero : (0, 0) ∈ J) : J ∩ vertices ⊆ {(0, 0)} := by
  obtain ⟨C, D, V, _, _, _, hC, hD, hCD, hinter, _, _, hCv, hDv⟩ :=
    exists_corner_arc_cut ha hb hW hproper
  have hsep : J ∩ (C ∩ D) = ∅ := by
    rw [hinter]
    exact disjoint_iff_inter_eq_empty.mp hJW
  have hJC : J ⊆ C := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hJ C D
        hC.isCompact.isClosed hD.isCompact.isClosed (hJsub.trans hCD.symm.subset) hsep with h | h
    · exact h
    · have hz := hDv.subset ⟨h hzero, Or.inl rfl⟩
      norm_num at hz
  exact fun _ hx => hCv.subset ⟨hJC hx.1, hx.2⟩

theorem vertices_avoid_normal_family {ι : Type*}
    (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hpv : ∀ k, p k ∉ vertices) (hqv : ∀ k, q k ∉ vertices) :
    vertices ⊆ base \ ⋃ k, D k := by
  intro x hx
  refine ⟨isFinitePLBallPair_base.1 (vertices_subset_frontier hx), ?_⟩
  intro hu
  obtain ⟨k, hk⟩ := mem_iUnion.mp hu
  rcases (hrim k).symm.subset ⟨hk, vertices_subset_frontier hx⟩ with h | h
  · exact hpv k (h ▸ hx)
  · exact hqv k ((mem_singleton_iff.mp h) ▸ hx)

theorem normal_corner_vertex_components_ne {ι : Type*}
    (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hsub : ∀ k, D k ⊆ base)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hpv : ∀ k, p k ∉ vertices) (hqv : ∀ k, q k ∉ vertices)
    (i : ι) (c d : Fin 3) (hcd : c ≠ d) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (htype : cornerMap c '' ({p i, q i} : Set (ℝ × ℝ)) = {(0, b), (a, 0)}) :
    connectedComponentIn (base \ ⋃ k, D k) (cornerVertex c) ≠
      connectedComponentIn (base \ ⋃ k, D k) (cornerVertex d) := by
  let R : Set (ℝ × ℝ) := base \ ⋃ k, D k
  let J := cornerMap c '' connectedComponentIn R (cornerVertex c)
  have hver (e : Fin 3) : cornerVertex e ∈ R :=
    vertices_avoid_normal_family D p q hrim hpv hqv (cornerVertex_mem e)
  have hW : IsFinitePLBallPair ℝ (cornerMap c '' D i) {(0, b), (a, 0)} := by
    rw [← htype]
    exact (hD i).affine_image (cornerMap c) (cornerMap_involutive c).injective.injOn
  have hproper : (cornerMap c '' D i) \ {(0, b), (a, 0)} ⊆ base \ frontier base := by
    rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    refine ⟨(cornerMap_mem_base c x).mpr (hsub i hx), ?_⟩
    intro hy
    exact hnot (htype.subset (mem_image_of_mem _ ((hrim i).symm.subset
      ⟨hx, (cornerMap_mem_frontier c x).mp hy⟩)))
  have hJ : IsPreconnected J := isPreconnected_connectedComponentIn.image _
    (cornerMap c).continuous.continuousOn
  have hJbase : J ⊆ base := by
    rintro _ ⟨x, hx, rfl⟩
    exact (cornerMap_mem_base c x).mpr (connectedComponentIn_subset _ _ hx).1
  have hJW : Disjoint J (cornerMap c '' D i) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hyx := (cornerMap_involutive c).injective he
    exact (connectedComponentIn_subset _ _ hx).2 (mem_iUnion.mpr ⟨i, hyx ▸ hy⟩)
  have hzero : (0, 0) ∈ J := by
    exact ⟨cornerVertex c, mem_connectedComponentIn (hver c), cornerMap_involutive c (0, 0)⟩
  intro he
  have hother : cornerMap c (cornerVertex d) ∈ J :=
    mem_image_of_mem _ (he.symm ▸ mem_connectedComponentIn (hver d))
  have hvertex := (cornerMap_image_vertices c).subset
    (mem_image_of_mem _ (cornerVertex_mem d))
  have hz := preconnected_corner_vertex_isolated ha hb hW hproper hJ hJbase hJW hzero
    ⟨hother, hvertex⟩
  exact hcd ((cornerMap_cornerVertex_eq_zero_iff c d).mp hz).symm

theorem corner_edgeIntervals_disjoint_vertices (c : Fin 3) {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : u < 1) (hv : v < 1) :
    Disjoint (cornerMap c '' edgeIntervals a b u v) vertices := by
  have hdis : Disjoint (edgeIntervals a b u v) vertices := by
    apply disjoint_left.mpr
    intro x hx hxv
    rcases hxv with rfl | rfl | rfl
    all_goals
      rcases hx with ⟨hx, hy⟩ | ⟨hx, hy⟩
      all_goals
        simp only [mem_singleton_iff, mem_Icc] at hx hy
        first | exact ha.not_ge hx.1 | exact hb.not_ge hy.1 |
          exact hu.not_ge hx.2 | exact hv.not_ge hy.2
  apply disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ hxv
  have hvx := (cornerMap_image_vertices c).subset (mem_image_of_mem (cornerMap c) hxv)
  rw [cornerMap_involutive c x] at hvx
  exact disjoint_left.mp hdis hx hvx

theorem rectangle_with_interior_edge_intervals_avoids_vertices
    {M : Set (ℝ × ℝ)} (c : Fin 3) {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : u < 1) (hv : v < 1)
    (hM : M ∩ frontier base = cornerMap c '' edgeIntervals a b u v) :
    Disjoint M vertices := by
  apply disjoint_left.mpr
  intro x hx hxv
  exact disjoint_left.mp (corner_edgeIntervals_disjoint_vertices c ha hb hu hv)
    (hM.subset ⟨hx, vertices_subset_frontier hxv⟩) hxv

end PoincareConjecture.M76.TriangleCorner

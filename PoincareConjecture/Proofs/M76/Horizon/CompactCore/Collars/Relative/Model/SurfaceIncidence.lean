import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceStars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FlatSphereIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private def normalFirstCoordinates : C3 ≃L[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x.2, x.1.1, x.1.2]
  invFun x := ((x 1, x 2), x 0)
  left_inv _ := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem exists_triangle_coface_of_planar_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) {p : E} (hps : p ∈ s)
    (a : E → P2) (ha : (K.closedStar p).AffineOnFaces a)
    (hai : InjOn a (K.closedStar p).space)
    (hint : a p ∈ interior (a '' (K.closedStar p).space)) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  classical
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  let J := ha.embeddedImage hai
  have hJ := ha.embeddedImage_finite hai (finite_closedStar_faces hK p)
  have hsJ : s.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space hsS)).mpr hsS
  have hintJ : a p ∈ interior J.space := by
    rw [ha.embeddedImage_space hai]
    exact hint
  obtain ⟨t, ht, hst, htc⟩ := J.exists_full_coface_of_hull_meets_interior hJ hsJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [ha.embeddedImage_faces hai] at ht
  obtain ⟨t, ht, rfl⟩ := ht
  refine ⟨t, ht.1, ?_, ?_⟩
  · intro x hxs
    obtain ⟨y, hyt, hyx⟩ := Finset.mem_image.mp (hst (Finset.mem_image.mpr ⟨x, hxs, rfl⟩))
    exact hai (S.subset_space ht hyt) (S.subset_space hsS hxs) hyx ▸ hyt
  · have hc := (Finset.card_image_iff.mpr (hai.mono (S.subset_space ht))).symm.trans htc
    simpa using hc

private theorem faceLink_ncard_eq_two_of_planar_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : E} (hps : p ∈ s) (a : E → P2)
    (ha : (K.closedStar p).AffineOnFaces a) (hai : InjOn a (K.closedStar p).space)
    (hint : a p ∈ interior (a '' (K.closedStar p).space)) :
    (K.faceLink s).vertices.ncard = 2 := by
  classical
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  let J := ha.embeddedImage hai
  have hJ := ha.embeddedImage_finite hai (finite_closedStar_faces hK p)
  have hsJ : s.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space hsS)).mpr hsS
  have hscJ : (s.image a).card = Module.finrank ℝ P2 := by
    rw [Finset.card_image_iff.mpr (hai.mono (S.subset_space hsS)), hs2]
    simp
  have hintJ : a p ∈ interior J.space := by
    rw [ha.embeddedImage_space hai]
    exact hint
  have hc := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hscJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [ha.ncard_embeddedImage_faceLink hai hsS] at hc
  have hlink : S.faceLink s = K.faceLink s := by
    rw [show S = K.closedFaceStar {p} from (K.closedFaceStar_singleton_eq_closedStar p).symm]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hlink] at hc

namespace CoorientedSurfaceStars

variable (T : CoorientedSurfaceStars E)

theorem rim_le_surface : T.marked 3 ≤ T.marked 2 :=
  T.ambient.le_of_common_subcomplex_space_subset (T.marked 3) (T.marked 2)
    (T.marked_le 3) (T.marked_le 2)
    (fun _ hx ↦ (T.surface_boundary_inter.symm.subset hx).1)

theorem rim_le_boundary : T.marked 3 ≤ T.marked 1 :=
  T.ambient.le_of_common_subcomplex_space_subset (T.marked 3) (T.marked 1)
    (T.marked_le 3) (T.marked_le 1)
    (fun _ hx ↦ (T.surface_boundary_inter.symm.subset hx).2)

theorem surface_vertex_mem_rim_iff_boundary (p : (T.marked 2).vertices) :
    (p : E) ∈ (T.marked 3).vertices ↔ (p : E) ∈ (T.marked 1).space := by
  constructor
  · exact fun hp ↦ (T.marked 1).vertices_subset_space (T.rim_le_boundary hp)
  · intro hp
    apply T.ambient.face_mem_subcomplex_of_intrinsicInterior (T.marked 3)
      (T.marked_le 3) (T.marked_le 2 p.property) (x := (p : E))
    · simp
    · exact T.surface_boundary_inter.subset
        ⟨(T.marked 2).vertices_subset_space p.property, hp⟩

theorem surface_face_mem_boundary_iff {s : Finset E} (hs : s ∈ (T.marked 2).faces) :
    s ∈ (T.marked 1).faces ↔ s ∈ (T.marked 3).faces := by
  refine ⟨?_, fun h ↦ T.rim_le_boundary h⟩
  intro hb
  apply T.marked_full 3 s (T.marked_le 2 hs)
  intro p hps
  have hp : p ∈ (T.marked 2).vertices :=
    (T.marked 2).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  exact (T.surface_vertex_mem_rim_iff_boundary ⟨p, hp⟩).mpr
    ((T.marked 1).subset_space hb hps)

omit [FiniteDimensional ℝ E] in
theorem surface_star_space (p : (T.marked 2).vertices) :
    ((T.marked 2).closedStar p).space =
      (T.ambient.closedStar p).space ∩ (T.marked 2).space :=
  T.ambient.closedStar_space_eq_inter_of_full (T.marked 2) T.finite
    (T.marked_le 2) (T.marked_full 2) p.property

omit [FiniteDimensional ℝ E] in
theorem surface_vertex_mem_star (p : (T.marked 2).vertices) :
    (p : E) ∈ (T.ambient.closedStar p).space := by
  apply (T.ambient.closedStar p).vertices_subset_space
  exact ⟨T.marked_le 2 p.property, by simpa using T.marked_le 2 p.property⟩

omit [FiniteDimensional ℝ E] in

theorem surface_star_planar (p : (T.marked 2).vertices) :
    ((T.marked 2).closedStar p).AffineOnFaces (fun x ↦ (T.chart p x).1) ∧
      InjOn (fun x ↦ (T.chart p x).1) ((T.marked 2).closedStar p).space := by
  let pi : C3 →ᴬ[ℝ] P2 := (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  have hs : (T.marked 2).closedStar p ≤ T.ambient.closedStar p :=
    fun _ hs ↦ ⟨T.marked_le 2 hs.1, T.marked_le 2 hs.2⟩
  have ha : ((T.marked 2).closedStar p).AffineOnFaces (T.chart p) :=
    fun _ ht ↦ T.star_affine p _ (hs ht)
  refine ⟨ha.postcomp pi, ?_⟩
  intro x hx y hy hxy
  have hx' := (T.surface_star_space p).subset hx
  have hy' := (T.surface_star_space p).subset hy
  apply T.star_injective p hx'.1 hy'.1
  exact Prod.ext hxy (((T.surface_eq p x hx'.1).mp hx'.2).2.trans
    ((T.surface_eq p y hy'.1).mp hy'.2).2.symm)

theorem surface_face_card_le_three {s : Finset E} (hs : s ∈ (T.marked 2).faces) :
    s.card ≤ 3 := by
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  have hp : p ∈ (T.marked 2).vertices :=
    (T.marked 2).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  exact (T.marked 2).face_card_le_three_of_planar_star hs hps
    (fun x ↦ (T.chart ⟨p, hp⟩ x).1)
    (T.surface_star_planar ⟨p, hp⟩).1 (T.surface_star_planar ⟨p, hp⟩).2

omit [FiniteDimensional ℝ E] in

theorem boundary_chart_model (p : (T.marked 2).vertices)
    (hp : (p : E) ∈ (T.marked 1).space) :
    (∀ x ∈ (T.ambient.closedStar p).space,
      x ∈ (T.marked 0).space ↔ 0 ≤ (T.chart p x).1.1) ∧
    ∀ x ∈ (T.ambient.closedStar p).space,
      x ∈ (T.marked 1).space ↔ (T.chart p x).1.1 = 0 := by
  rcases T.chart_model p with h | h
  · exact False.elim (Set.disjoint_left.mp h.2 (T.surface_vertex_mem_star p) hp)
  · exact h

theorem rim_face_card_le_two {s : Finset E} (hs : s ∈ (T.marked 3).faces) :
    s.card ≤ 2 := by
  obtain ⟨p, hps⟩ := (T.marked 3).nonempty_of_mem_faces hs
  have hpR : p ∈ (T.marked 3).vertices :=
    (T.marked 3).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  let pS : (T.marked 2).vertices := ⟨p, T.rim_le_surface hpR⟩
  have hmodel := T.boundary_chart_model pS
    ((T.surface_vertex_mem_rim_iff_boundary pS).mp hpR)
  have hRS : (T.marked 3).closedStar p ≤ (T.marked 2).closedStar p :=
    fun _ ht ↦ ⟨T.rim_le_surface ht.1, T.rim_le_surface ht.2⟩
  have hRA : (T.marked 3).closedStar p ≤ T.ambient.closedStar p :=
    fun _ ht ↦ ⟨T.marked_le 3 ht.1, T.marked_le 3 ht.2⟩
  apply (T.marked 3).face_card_le_two_of_planar_line_star hs hps
    (fun x ↦ (T.chart pS x).1)
    (fun _ ht ↦ (T.surface_star_planar pS).1 _ (hRS ht))
    ((T.surface_star_planar pS).2.mono (space_subset_of_le hRS))
  intro x hx
  apply (hmodel.2 x (space_subset_of_le hRA hx)).mp
  exact space_subset_of_le T.rim_le_boundary
    (space_subset_of_le (show (T.marked 3).closedStar p ≤ T.marked 3 from fun _ ht ↦ ht.1) hx)

omit [FiniteDimensional ℝ E] in

theorem exists_surface_planar_star (p : (T.marked 2).vertices)
    (hinside : (T.ambient.closedStar p).space ⊆ (T.marked 0).space) :
    ∃ a : E → P2, ((T.marked 2).closedStar p).AffineOnFaces a ∧
      InjOn a ((T.marked 2).closedStar p).space ∧
      a p ∈ interior (a '' ((T.marked 2).closedStar p).space) := by
  let c := normalFirstCoordinates
  apply T.ambient.exists_planar_star_of_flat_ambient_star (T.marked 2) T.finite
    (T.marked_le 2) (T.marked_full 2) p.property (c ∘ T.chart p)
    ((T.star_affine p).postcomp c.toContinuousAffineEquiv.toContinuousAffineMap)
    (fun _ hx _ hy he ↦ T.star_injective p hx hy (c.injective he))
  · change c (T.chart p p) ∈ interior ((c ∘ T.chart p) '' (T.ambient.closedStar p).space)
    rw [Set.image_comp]
    exact c.toHomeomorph.isOpenMap.image_interior_subset _
      ⟨T.chart p p, T.star_interior p, rfl⟩
  · intro x hx
    change x ∈ (T.marked 2).space ↔ (T.chart p x).2 = 0
    rw [T.surface_eq p x hx]
    exact and_iff_right (hinside hx)

omit [FiniteDimensional ℝ E] in

theorem exists_surface_halfPlane_star (p : (T.marked 2).vertices)
    (hregion : ∀ x ∈ (T.ambient.closedStar p).space,
      x ∈ (T.marked 0).space ↔ 0 ≤ (T.chart p x).1.1) :
    ∃ (a : E → P2) (U : Set P2),
      ((T.marked 2).closedStar p).AffineOnFaces a ∧
      InjOn a ((T.marked 2).closedStar p).space ∧ IsOpen U ∧ a p ∈ U ∧
      a '' ((T.marked 2).closedStar p).space ⊆ {z | 0 ≤ z.1} ∧
      U ∩ {z | 0 ≤ z.1} ⊆ a '' ((T.marked 2).closedStar p).space ∧
      ∀ x, a x = (T.chart p x).1 := by
  apply T.ambient.exists_halfPlane_star_of_quadrant_ambient_star (T.marked 2) T.finite
    (T.marked_le 2) (T.marked_full 2) p.property (T.chart p)
    (T.star_affine p) (T.star_injective p) (T.star_interior p)
  intro x hx
  rw [T.surface_eq p x hx, hregion x hx]

theorem surface_exists_triangle_coface {s : Finset E} (hs : s ∈ (T.marked 2).faces) :
    ∃ t ∈ (T.marked 2).faces, s ⊆ t ∧ t.card = 3 := by
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  have hp : p ∈ (T.marked 2).vertices :=
    (T.marked 2).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  rcases T.chart_model ⟨p, hp⟩ with h | h
  · obtain ⟨a, ha, hai, hint⟩ := T.exists_surface_planar_star ⟨p, hp⟩ h.1
    exact exists_triangle_coface_of_planar_star (T.marked 2) (T.marked_finite 2)
      hs hps a ha hai hint
  · obtain ⟨a, U, ha, hai, hU, hpU, hhalf, hUS, _⟩ :=
      T.exists_surface_halfPlane_star ⟨p, hp⟩ h.1
    exact (T.marked 2).exists_triangle_coface_of_halfPlane_star (T.marked_finite 2)
      hs hps a ha hai hU hpU hhalf hUS

theorem surface_edge_faceLink_ncard_eq_one {s : Finset E}
    (hs : s ∈ (T.marked 3).faces) (hs2 : s.card = 2) :
    ((T.marked 2).faceLink s).vertices.ncard = 1 := by
  obtain ⟨p, hps⟩ := (T.marked 3).nonempty_of_mem_faces hs
  have hpR : p ∈ (T.marked 3).vertices :=
    (T.marked 3).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  let pS : (T.marked 2).vertices := ⟨p, T.rim_le_surface hpR⟩
  have hmodel := T.boundary_chart_model pS
    ((T.surface_vertex_mem_rim_iff_boundary pS).mp hpR)
  obtain ⟨a, U, ha, hai, hU, hpU, hhalf, hUS, hval⟩ :=
    T.exists_surface_halfPlane_star pS hmodel.1
  apply (T.marked 2).faceLink_ncard_eq_one_of_halfPlane_star (T.marked_finite 2)
    (T.rim_le_surface hs) hs2 hps a ha hai hU hpU hhalf hUS
  intro x hxs
  rw [hval x]
  have hsA : s ∈ (T.ambient.closedStar p).faces :=
    ⟨T.marked_le 3 hs, by simpa [Finset.insert_eq_of_mem hps] using T.marked_le 3 hs⟩
  exact (hmodel.2 x ((T.ambient.closedStar p).subset_space hsA hxs)).mp
    ((T.marked 1).subset_space (T.rim_le_boundary hs) hxs)

theorem surface_edge_faceLink_ncard_eq_two {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hs2 : s.card = 2)
    (hrim : s ∉ (T.marked 3).faces) :
    ((T.marked 2).faceLink s).vertices.ncard = 2 := by
  classical
  have hex : ∃ p ∈ s, p ∉ (T.marked 3).vertices := by
    by_contra h
    push Not at h
    exact hrim (T.marked_full 3 s (T.marked_le 2 hs) h)
  obtain ⟨p, hps, hpR⟩ := hex
  have hp : p ∈ (T.marked 2).vertices :=
    (T.marked 2).down_closed hs (Finset.singleton_subset_iff.mpr hps)
      (Finset.singleton_nonempty p)
  let pS : (T.marked 2).vertices := ⟨p, hp⟩
  rcases T.chart_model pS with h | h
  · obtain ⟨a, ha, hai, hint⟩ := T.exists_surface_planar_star pS h.1
    exact faceLink_ncard_eq_two_of_planar_star (T.marked 2) (T.marked_finite 2)
      hs hs2 hps a ha hai hint
  · obtain ⟨a, U, ha, hai, hU, hpU, _, hUS, hval⟩ :=
      T.exists_surface_halfPlane_star pS h.1
    apply (T.marked 2).faceLink_ncard_eq_two_of_halfPlane_star (T.marked_finite 2)
      hs hs2 hps a ha hai hU hpU hUS
    rw [hval p]
    have hnonneg : 0 ≤ (T.chart pS p).1.1 :=
      (h.1 p (T.surface_vertex_mem_star pS)).mp
        (T.surface_subset_region ((T.marked 2).vertices_subset_space hp))
    have hne : (T.chart pS p).1.1 ≠ 0 := by
      intro hz
      exact hpR ((T.surface_vertex_mem_rim_iff_boundary pS).mpr
        ((h.2 p (T.surface_vertex_mem_star pS)).mpr hz))
    exact lt_of_le_of_ne hnonneg hne.symm

theorem surface_edge_faceLink_ncard {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hs2 : s.card = 2) :
    (s ∈ (T.marked 3).faces ∧ ((T.marked 2).faceLink s).vertices.ncard = 1) ∨
      (s ∉ (T.marked 3).faces ∧ ((T.marked 2).faceLink s).vertices.ncard = 2) := by
  classical
  by_cases hrim : s ∈ (T.marked 3).faces
  · exact Or.inl ⟨hrim, T.surface_edge_faceLink_ncard_eq_one hrim hs2⟩
  · exact Or.inr ⟨hrim, T.surface_edge_faceLink_ncard_eq_two hs hs2 hrim⟩

end CoorientedSurfaceStars
end Geometry.SimplicialComplex

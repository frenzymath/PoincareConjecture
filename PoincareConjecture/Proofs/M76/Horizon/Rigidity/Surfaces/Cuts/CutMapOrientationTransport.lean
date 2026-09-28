import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutInteriorHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutRectangle
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import PoincareConjecture.Proofs.M76.Mathlib.AffineMapSubdivision
import Mathlib.Topology.Connected.TotallyDisconnected










set_option autoImplicit false

open Set Geometry Classical Topology
open PreAbstractSimplicialComplex.ModTwoCochains

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem injOn_convex_of_finite_fibers (a : E →ᵃ[ℝ] F) {s : Set E}
    (hs : Convex ℝ s) (hf : ∀ y, (s ∩ a ⁻¹' {y}).Finite) : InjOn a s := by
  intro x hx y hy heq
  have hc : Convex ℝ (s ∩ a ⁻¹' {a x}) :=
    hs.inter ((convex_singleton (a x)).affine_preimage a)
  have hsub := hc.isPreconnected.isDiscrete_iff_subsingleton.mp (hf (a x)).isDiscrete
  exact hsub ⟨hx, rfl⟩ ⟨hy, heq.symm⟩

end AffineMap

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem injOn_starConvex_of_nhds (a : E →ₗ[ℝ] F) {s U : Set E} {c : E}
    (hs : StarConvex ℝ c s) (hU : U ∈ 𝓝 c) (hi : InjOn a (s ∩ U)) : InjOn a s := by
  intro x hx y hy hxy
  have hnear (z : E) : {t : ℝ | (1 - t) • c + t • z ∈ U} ∈ 𝓝 0 := by
    have hc : Continuous (fun t : ℝ ↦ (1 - t) • c + t • z) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ ↦ (1 - t) • c + t • z) (𝓝 0) (𝓝 c) := by
      simpa using hc.tendsto 0
    exact ht hU
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (Filter.inter_mem (hnear x) (hnear y))
  let r : ℝ := min (u / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hu) (by norm_num)
  have hru : r < u := (min_le_left _ _).trans_lt (half_lt_self hu)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hmem := hsub ⟨hl.trans hr, hru⟩
  have he := hi ⟨hs hx (sub_nonneg.mpr hr1) hr.le (sub_add_cancel _ _), hmem.1⟩
    ⟨hs hy (sub_nonneg.mpr hr1) hr.le (sub_add_cancel _ _), hmem.2⟩
    (by simp only [map_add, map_smul, hxy])
  exact smul_right_injective _ hr.ne' (add_left_cancel he)

end LinearMap

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L : SimplicialComplex ℝ E} {f : E → F}

omit [FiniteDimensional ℝ E] in
theorem AffineOnFaces.injOn_hull_of_finite_fibers (hf : L.AffineOnFaces f)
    (hfib : ∀ y, (L.space ∩ f ⁻¹' {y}).Finite) {s : Finset E} (hs : s ∈ L.faces) :
    InjOn f (convexHull ℝ (s : Set E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hi : InjOn a (convexHull ℝ (s : Set E)) :=
    a.toAffineMap.injOn_convex_of_finite_fibers (convex_convexHull ℝ _)
      (fun y ↦ (hfib y).subset (fun x hx ↦
        ⟨L.convexHull_subset_space hs hx.1, (ha hx.1).trans hx.2⟩))
  exact fun x hx y hy hxy ↦ hi hx hy ((ha hx).symm.trans (hxy.trans (ha hy)))

theorem AffineOnFaces.affineIndependent_of_finite_fibers (hf : L.AffineOnFaces f)
    (hfib : ∀ y, (L.space ∩ f ⁻¹' {y}).Finite) {s : Finset E} (hs : s ∈ L.faces) :
    AffineIndependent ℝ (f ∘ ((↑) : s → E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hinj := hf.injOn_hull_of_finite_fibers hfib hs
  have hi : InjOn a (convexHull ℝ (range ((↑) : s → E))) := by
    rw [Subtype.range_coe]
    exact fun x hx y hy hxy ↦ hinj hx hy ((ha hx).trans (hxy.trans (ha hy).symm))
  have hind := a.toAffineMap.affineIndependent_comp_of_injOn_convexHull (L.indep hs) hi
  have heq : a.toAffineMap ∘ ((↑) : s → E) = f ∘ ((↑) : s → E) := by
    funext x
    exact (ha (subset_convexHull ℝ _ x.property)).symm
  rwa [heq] at hind

omit [FiniteDimensional ℝ E] in
theorem AffineOnFaces.starConvex_image_closedFaceStar [DecidableEq E]
    (hf : L.AffineOnFaces f) (s : Finset E) {c : E}
    (hc : c ∈ convexHull ℝ (s : Set E)) :
    StarConvex ℝ (f c) (f '' (L.closedFaceStar s).space) := by
  rintro _ ⟨x, hx, rfl⟩ a b ha hb hab
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hsu : s ∪ t ∈ (L.closedFaceStar s).faces :=
    ⟨ht.2, by simpa only [← Finset.union_assoc, Finset.union_self] using ht.2⟩
  obtain ⟨g, hg⟩ := hf (s ∪ t) ht.2
  have hc' : c ∈ convexHull ℝ ((s ∪ t : Finset E) : Set E) :=
    convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_left) hc
  have hx' : x ∈ convexHull ℝ ((s ∪ t : Finset E) : Set E) :=
    convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_right) hxt
  have hcv := (convex_convexHull ℝ ((s ∪ t : Finset E) : Set E)).affine_image g.toAffineMap
  obtain ⟨z, hz, hvalue⟩ := hcv ⟨c, hc', (hg hc').symm⟩
    ⟨x, hx', (hg hx').symm⟩ ha hb hab
  exact ⟨z, (L.closedFaceStar s).convexHull_subset_space hsu hz, (hg hz).trans hvalue⟩

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

include hbound

theorem sourceMap_fiber_finite (x : E) :
    (A.carrier ∩ A.sourceMap ⁻¹' {x}).Finite := by
  by_cases hxK : x ∈ K.space
  · by_cases hxc : x = A.sectors.center
    · subst x
      rw [A.sourceMap_center_fiber hbound]
      exact finite_range _
    · by_cases hsp : x ∈ ⋃ i, A.sectors.spoke i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hsp
        rw [A.sourceMap_spoke_fiber hbound i hi hxc]
        exact (finite_singleton _).insert _
      · by_cases hb : x ∈ residualBridgeUnion K P D hcofaces A.bands
        · obtain ⟨s, hs⟩ := mem_iUnion.mp hb
          have hnP : x ∉ K.barycentricSubdivision.vertexDualUnion
              (primalCentroidSet K P hP) := fun hx ↦
            hsp (A.bridge_primal_subset_spokes s hs hx)
          rw [A.sourceMap_bridge_fiber hbound s hs hnP]
          exact (finite_singleton _).insert _
        · obtain ⟨p, hp⟩ := A.sourceMap_singleton_off_spokes_and_bridges
            hbound hxK hsp hb
          rw [hp]
          exact finite_singleton _
  · have hempty : A.carrier ∩ A.sourceMap ⁻¹' {x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro p ⟨hp, heq⟩
      exact hxK (heq ▸ A.sourceMap_image.subset (mem_image_of_mem _ hp))
    rw [hempty]
    exact finite_empty



theorem sourceMap_injOn_convex
    {s : Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))}
    (hs : Convex ℝ s) (hscarrier : s ⊆ A.carrier) : InjOn A.sourceMap s := by
  let a := ((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
    (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ))
      (Fin 4 → ℝ))).toAffineMap
  exact a.injOn_convex_of_finite_fibers hs (fun y ↦
    (A.sourceMap_fiber_finite hbound y).subset (inter_subset_inter_left _ hscarrier))



theorem sourceMap_injOn_starConvex
    {s : Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))}
    {c : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hc : c ∈ A.carrier \ A.rim) (hs : StarConvex ℝ c s) (hscarrier : s ⊆ A.carrier) :
    InjOn A.sourceMap s := by
  let a := ((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
    (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ))
      (Fin 4 → ℝ)))
  have hcut : a c ∉ A.cutGraph := by
    exact fun h ↦ hc.2 (A.mem_rim_of_sourceMap_mem_cutGraph hbound hc.1 h)
  have hU : a ⁻¹' A.cutGraphᶜ ∈ 𝓝 c :=
    ((A.cutGraph_isCompact hbound).isClosed.isOpen_compl.preimage a.continuous).mem_nhds hcut
  apply a.toLinearMap.injOn_starConvex_of_nhds hs hU
  intro x hx y hy hxy
  apply A.sourceMap_injOn_interior hbound
    ⟨hscarrier hx.1, fun h ↦ hx.2 (A.sourceMap_rim_image.subset (mem_image_of_mem _ h))⟩
    ⟨hscarrier hy.1, fun h ↦ hy.2 (A.sourceMap_rim_image.subset (mem_image_of_mem _ h))⟩ hxy

theorem sourceMap_injOn_closedFaceStar
    (L : SimplicialComplex ℝ
      ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    (hL : L.space ⊆ A.carrier) (s : Finset
      ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    {c : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hc : c ∈ A.carrier \ A.rim) (hcs : c ∈ convexHull ℝ (s : Set _)) :
    InjOn A.sourceMap (L.closedFaceStar s).space := by
  exact A.sourceMap_injOn_starConvex hbound hc (L.starConvex_closedFaceStar s hcs)
    (fun x hx ↦ hL (SimplicialComplex.space_subset_of_le (L.closedFaceStar_le s) hx))



theorem sourceMap_comp_injOn_closedFaceStar
    (L : SimplicialComplex ℝ (ℝ × ℝ))
    (f : (ℝ × ℝ) → ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    (hf : L.AffineOnFaces f) (hfi : InjOn f L.space)
    (hmap : MapsTo f L.space A.carrier) (s : Finset (ℝ × ℝ)) {c : ℝ × ℝ}
    (hc : f c ∈ A.carrier \ A.rim) (hcs : c ∈ convexHull ℝ (s : Set (ℝ × ℝ))) :
    InjOn (A.sourceMap ∘ f) (L.closedFaceStar s).space := by
  have hsub := SimplicialComplex.space_subset_of_le (L.closedFaceStar_le s)
  have hi := A.sourceMap_injOn_starConvex hbound hc
    (hf.starConvex_image_closedFaceStar s hcs)
    (image_subset_iff.mpr (fun _ hx ↦ hmap (hsub hx)))
  intro x hx y hy hxy
  exact hfi (hsub hx) (hsub hy) (hi (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy)

theorem sourceMap_affineIndependent
    {s : Finset ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))}
    (hs : AffineIndependent ℝ ((↑) : s →
      ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))))
    (hscarrier : convexHull ℝ (s : Set _) ⊆ A.carrier) :
    AffineIndependent ℝ (A.sourceMap ∘ ((↑) : s → _)) := by
  let a := ((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
    (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ))
      (Fin 4 → ℝ))).toAffineMap
  apply a.affineIndependent_comp_of_injOn_convexHull hs
  rw [Subtype.range_coe]
  exact A.sourceMap_injOn_convex hbound (convex_convexHull ℝ _) hscarrier

theorem sourceMap_card_le_owner
    {s : Finset ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))}
    (hs : AffineIndependent ℝ ((↑) : s →
      ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))))
    (hscarrier : convexHull ℝ (s : Set _) ⊆ A.carrier)
    {t : Finset E}
    (howner : MapsTo A.sourceMap (convexHull ℝ (s : Set _))
      (convexHull ℝ (t : Set E))) : s.card ≤ t.card := by
  have hi := A.sourceMap_injOn_convex hbound (convex_convexHull ℝ _) hscarrier
  have hind := (A.sourceMap_affineIndependent hbound hs hscarrier).range
  have hrange : range (A.sourceMap ∘ ((↑) : s →
      ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))) =
      (s.image A.sourceMap : Set E) := by
    ext x
    simp
  rw [hrange] at hind
  have hcard := hind.card_le_card_of_subset_affineSpan (t := t) (by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (convexHull_subset_affineSpan (t : Set E))
      (howner (subset_convexHull ℝ _ hy)))
  have hvertex : InjOn A.sourceMap (s : Set _) :=
    hi.mono (subset_convexHull ℝ _)
  rwa [Finset.card_image_of_injOn hvertex] at hcard



theorem exists_original_face_refinement :
    ∃ L : SimplicialComplex ℝ
        ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)),
      L.faces.Finite ∧ L.space = A.carrier ∧ L.AffineOnFaces A.sourceMap ∧
      (∀ s ∈ L.faces, InjOn A.sourceMap (convexHull ℝ (s : Set _))) ∧
      (∀ s ∈ L.faces, AffineIndependent ℝ (A.sourceMap ∘ ((↑) : s → _))) ∧
      ∀ s ∈ L.faces, ∃ t ∈ K.faces,
        MapsTo A.sourceMap (convexHull ℝ (s : Set _)) (convexHull ℝ (t : Set E)) := by
  obtain ⟨J, hJ, hJs, hJmap⟩ := A.sourceMapPL
  change J.space = A.carrier at hJs
  have hN : ∀ s ∈ J.faces, s.card ≤ hJ.toFinset.sup Finset.card + 1 := by
    intro s hs
    exact (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ _)
  have hcover : ∀ x ∈ J.space, ∃ t : K.faces,
      (A.sourceMap) x ∈ convexHull ℝ (t.val : Set E) := by
    intro x hx
    have hxK := A.sourceMap_image.subset (mem_image_of_mem A.sourceMap (hJs.subset hx))
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxK
    exact ⟨⟨t, ht⟩, hxt⟩
  obtain ⟨L, hL, hLJ, _, hfaces⟩ := hJmap.exists_subdivision_mapsTo_cover hJ hN
    ((↑) : K.faces → Finset E) (fun t ↦ K.indep t.property) hcover
  have hLs : L.space = A.carrier := hLJ.space_eq.trans hJs
  refine ⟨L, hL, hLs, hLJ.affineOnFaces hJmap, ?_, ?_, ?_⟩
  · intro s hs
    exact A.sourceMap_injOn_convex hbound (convex_convexHull ℝ _)
      (fun x hx ↦ hLs.subset (L.convexHull_subset_space hs hx))
  · intro s hs
    exact A.sourceMap_affineIndependent hbound (L.indep hs)
      (fun x hx ↦ hLs.subset (L.convexHull_subset_space hs hx))
  · intro s hs
    obtain ⟨t, ht⟩ := hfaces s hs
    exact ⟨t.val, t.property, ht⟩



theorem exists_original_triangle_refinement
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 3) :
    ∃ L : SimplicialComplex ℝ
        ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)),
      L.faces.Finite ∧ L.space = A.carrier ∧ L.AffineOnFaces A.sourceMap ∧
      (∀ s ∈ L.faces, s.card ≤ 3) ∧
      (∀ s ∈ L.faces, InjOn A.sourceMap (convexHull ℝ (s : Set _))) ∧
      (∀ s ∈ L.faces, AffineIndependent ℝ (A.sourceMap ∘ ((↑) : s → _))) ∧
      ∀ s ∈ L.faces, ∃ t ∈ K.faces, t.card = 3 ∧
        MapsTo A.sourceMap (convexHull ℝ (s : Set _)) (convexHull ℝ (t : Set E)) := by
  obtain ⟨L, hL, hLs, hmap, hinj, hind, howners⟩ :=
    A.exists_original_face_refinement hbound
  refine ⟨L, hL, hLs, hmap, ?_, hinj, hind, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := howners s hs
    exact (A.sourceMap_card_le_owner hbound (L.indep hs)
      (fun x hx ↦ hLs.subset (L.convexHull_subset_space hs hx)) hst).trans (hbound t ht)
  · intro s hs
    obtain ⟨t, ht, hst⟩ := howners s hs
    obtain ⟨u, hu, htu, huc⟩ := hpure t ht
    exact ⟨u, hu, huc, fun _ hx ↦ convexHull_mono htu (hst hx)⟩



theorem exists_marked_planar_original_refinement
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 3) :
    ∃ C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier, C.IsFinitePL ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1) ∧
      ∃ (f : (ℝ × ℝ) →
          ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
        (F : (ℝ × ℝ) → E) (L : SimplicialComplex ℝ (ℝ × ℝ)),
        (∀ x, f x.val = (C x).val) ∧ F = A.sourceMap ∘ f ∧ L.AffineOnFaces f ∧
        (∀ x, F x.val = (A.sourceMap) (C x)) ∧
        L.faces.Finite ∧ L.space = PeriodicSquare.squareCarrier 1 ∧
        L.AffineOnFaces F ∧ F '' L.space = K.space ∧
        (∀ s ∈ L.faces, InjOn F (convexHull ℝ (s : Set (ℝ × ℝ)))) ∧
        (∀ s ∈ L.faces, AffineIndependent ℝ (F ∘ ((↑) : s → ℝ × ℝ))) ∧
        ∀ s ∈ L.faces, ∃ t ∈ K.faces, t.card = 3 ∧
          MapsTo F (convexHull ℝ (s : Set (ℝ × ℝ))) (convexHull ℝ (t : Set E)) := by
  obtain ⟨C, hC, hw, hz, hl, hr⟩ := A.exists_marked_cut_rectangle hbound
  obtain ⟨f, hf, hval⟩ := hC
  have hmap : MapsTo f (PeriodicSquare.squareCarrier 1) A.carrier := by
    intro x hx
    rw [← hval ⟨x, hx⟩]
    exact (C ⟨x, hx⟩).property
  have hfi : InjOn f (PeriodicSquare.squareCarrier 1) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (heq.trans (hval ⟨y, hy⟩).symm))))
  have himage : f '' PeriodicSquare.squareCarrier 1 = A.carrier := by
    apply Subset.antisymm
    · exact image_subset_iff.mpr hmap
    · intro y hy
      obtain ⟨x, hx⟩ := C.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hval x).symm.trans (congrArg Subtype.val hx)⟩
  let F := A.sourceMap ∘ f
  obtain ⟨J, hJ, hJs, hJf⟩ := hf
  let a := ((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
    (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ))
      (Fin 4 → ℝ))).toContinuousAffineMap
  have hJmap : J.AffineOnFaces F := hJf.postcomp a
  have hN : ∀ s ∈ J.faces, s.card ≤ hJ.toFinset.sup Finset.card + 1 := by
    intro s hs
    exact (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ _)
  have hcover : ∀ x ∈ J.space, ∃ t : K.faces, F x ∈ convexHull ℝ (t.val : Set E) := by
    intro x hx
    have hxK := A.sourceMap_image.subset (mem_image_of_mem A.sourceMap (hmap (hJs.subset hx)))
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxK
    exact ⟨⟨t, ht⟩, hxt⟩
  obtain ⟨L, hL, hLJ, _, howners⟩ := hJmap.exists_subdivision_mapsTo_cover hJ hN
    ((↑) : K.faces → Finset E) (fun t ↦ K.indep t.property) hcover
  have hLs := hLJ.space_eq.trans hJs
  have hLmap : L.AffineOnFaces F := hLJ.affineOnFaces hJmap
  have hfib (y : E) : (L.space ∩ F ⁻¹' {y}).Finite := by
    have him : f '' (L.space ∩ F ⁻¹' {y}) ⊆ A.carrier ∩ A.sourceMap ⁻¹' {y} := by
      rintro p ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨hmap (hLs.subset hx), hxy⟩
    exact ((A.sourceMap_fiber_finite hbound y).subset him).of_finite_image
      (hfi.mono (inter_subset_left.trans hLs.subset))
  refine ⟨C, ⟨f, ⟨J, hJ, hJs, hJf⟩, hval⟩, hw, hz, hl, hr, f, F, L,
    (fun x ↦ (hval x).symm), rfl, hLJ.affineOnFaces hJf, ?_, hL, hLs, hLmap, ?_,
    (fun _ hs ↦ hLmap.injOn_hull_of_finite_fibers hfib hs),
    (fun _ hs ↦ hLmap.affineIndependent_of_finite_fibers hfib hs), ?_⟩
  · intro x
    exact congrArg A.sourceMap (hval x).symm
  · change (A.sourceMap ∘ f) '' L.space = K.space
    rw [image_comp, hLs, himage]
    exact A.sourceMap_image
  · intro s hs
    obtain ⟨t, hst⟩ := howners s hs
    obtain ⟨u, hu, htu, huc⟩ := hpure t.val t.property
    exact ⟨u, hu, huc, fun _ hx ↦ convexHull_mono htu (hst hx)⟩

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkGraphCoordinates










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {s : Finset E} {g : E → ℝ × E}





theorem AffineOnFaces.graph_off_face_lineMap (hg : K.AffineOnFaces g)
    (hgv : ∀ v ∈ K.vertices, g v = if v ∈ s then 0 else (1, v))
    {x y : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hy : y ∈ (K.faceLink s).space)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    AffineMap.lineMap x y r ∈ (K.closedFaceStar s).space ∧
      AffineMap.lineMap x y r ∉ affineSpan ℝ (s : Set E) ∧
      g (AffineMap.lineMap x y r) = (r, r • y) := by
  classical
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
  let u := s ∪ t
  have hu : u ∈ K.faces := ht.2.2
  obtain ⟨a, ha⟩ := hg u hu
  have hxU : x ∈ convexHull ℝ (u : Set E) := convexHull_mono Finset.subset_union_left hx
  have hyU : y ∈ convexHull ℝ (u : Set E) := convexHull_mono Finset.subset_union_right hyt
  have hzU : AffineMap.lineMap x y r ∈ convexHull ℝ (u : Set E) :=
    (convex_convexHull ℝ _).lineMap_mem hxU hyU ⟨hr.1.le, hr.2⟩
  have hvK (v : E) (hv : v ∈ u) : v ∈ K.vertices := by
    rw [vertices_eq]
    exact mem_biUnion hu hv
  have hazero : EqOn a.toAffineMap (AffineMap.const ℝ E (0 : ℝ × E)) (s : Set E) := by
    intro v hv
    change v ∈ s at hv
    have hvU : v ∈ u := Finset.mem_union_left t hv
    change a v = 0
    rw [← ha (subset_convexHull ℝ _ hvU), hgv v (hvK v hvU), if_pos hv]
  have hzero : ∀ z ∈ affineSpan ℝ (s : Set E), a z = 0 :=
    fun z hz => AffineMap.eqOn_affineSpan hazero hz
  let b : E →ᴬ[ℝ] ℝ × E :=
    (ContinuousAffineMap.const ℝ E (1 : ℝ)).prod (ContinuousAffineMap.id ℝ E)
  have hagraph : EqOn a.toAffineMap b.toAffineMap (t : Set E) := by
    intro v hv
    have hvU : v ∈ u := Finset.mem_union_right s hv
    have hvs : v ∉ s := fun h => Finset.disjoint_left.mp ht.2.1 h hv
    change a v = (1, v)
    rw [← ha (subset_convexHull ℝ _ hvU), hgv v (hvK v hvU), if_neg hvs]
  have hay : a y = (1, y) :=
    AffineMap.eqOn_affineSpan hagraph (convexHull_subset_affineSpan _ hyt)
  have hformula : g (AffineMap.lineMap x y r) = (r, r • y) := by
    rw [ha hzU]
    change a.toAffineMap (AffineMap.lineMap x y r) = _
    rw [AffineMap.apply_lineMap]
    change AffineMap.lineMap (a x) (a y) r = _
    rw [hzero x (convexHull_subset_affineSpan _ hx), hay]
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have huStar : u ∈ (K.closedFaceStar s).faces := ⟨hu, by
    simpa only [u, ← Finset.union_assoc, Finset.union_self] using hu⟩
  refine ⟨(K.closedFaceStar s).convexHull_subset_space huStar hzU, ?_, hformula⟩
  intro hzspan
  have he : (r, r • y) = (0 : ℝ × E) :=
    hformula.symm.trans ((ha hzU).trans (hzero _ hzspan))
  exact hr.1.ne' (congrArg Prod.fst he)

variable [FiniteDimensional ℝ E]






theorem exists_continuous_faceLink_retraction
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (s : Finset E) :
    ∃ R : E → E,
      ContinuousOn R ((K.closedFaceStar s).space \ (affineSpan ℝ (s : Set E) : Set E)) ∧
      MapsTo R ((K.closedFaceStar s).space \ (affineSpan ℝ (s : Set E) : Set E))
        (K.faceLink s).space ∧
      ∀ x ∈ convexHull ℝ (s : Set E), ∀ y ∈ (K.faceLink s).space,
        ∀ r ∈ Ioc (0 : ℝ) 1,
          AffineMap.lineMap x y r ∈
            (K.closedFaceStar s).space \ (affineSpan ℝ (s : Set E) : Set E) ∧
          R (AffineMap.lineMap x y r) = y := by
  classical
  obtain ⟨g, hg, hgv⟩ := K.exists_affineOnFaces_eqOn_vertices
    (fun v => if v ∈ s then (0 : ℝ × E) else (1, v))
  have hgv' (v : E) (hv : v ∈ K.vertices) :
      g v = if v ∈ s then 0 else (1, v) := hgv hv
  let D := (K.closedFaceStar s).space \ (affineSpan ℝ (s : Set E) : Set E)
  have hDK : D ⊆ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx.1
    exact K.convexHull_subset_space ht.1 hxt
  let R : E → E := fun x => (g x).1⁻¹ • (g x).2
  have hgcont : ContinuousOn g D := (hg.continuousOn hK).mono hDK
  refine ⟨R, ?_, fun x hx => hg.graph_off_face_normalized_mem_link hgv' hx.1 hx.2, ?_⟩
  · exact (hgcont.fst.inv₀
      (fun x hx => (hg.graph_off_face_pos hgv' (hDK hx) hx.2).ne')).smul hgcont.snd
  · intro x hx y hy r hr
    obtain ⟨hzstar, hzoff, hformula⟩ := hg.graph_off_face_lineMap hgv' hx hy hr
    refine ⟨⟨hzstar, hzoff⟩, ?_⟩
    change (g (AffineMap.lineMap x y r)).1⁻¹ • (g (AffineMap.lineMap x y r)).2 = y
    rw [hformula]
    simp only [smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]

end Geometry.SimplicialComplex

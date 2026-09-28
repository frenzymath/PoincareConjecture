import PoincareConjecture.Proofs.M76.Mathlib.SupportedPLGraphCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import PoincareConjecture.Proofs.M76.Mathlib.ConeSimplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {s : Finset E} {g : E → ℝ × E}

theorem AffineOnFaces.graph_off_face_pos (hg : K.AffineOnFaces g)
    (hgv : ∀ v ∈ K.vertices, g v = if v ∈ s then 0 else (1, v))
    {x : E} (hx : x ∈ K.space) (hxoff : x ∉ affineSpan ℝ (s : Set E)) :
    0 < (g x).1 := by
  have hvertices (v : E) (hv : v ∈ K.vertices) : g v = 0 ∨ g v = (1, v) := by
    rw [hgv v hv]
    split_ifs <;> simp
  have hnonneg := (hg.graph_vertex_bounds hvertices hx).1
  apply lt_of_le_of_ne hnonneg
  intro he
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hg t ht
  let A : E →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ E).toAffineMap.comp a.toAffineMap
  have hAv (v : E) (hv : v ∈ t) : A v = if v ∈ s then 0 else 1 := by
    have hvK : v ∈ K.vertices := by rw [vertices_eq]; exact mem_biUnion ht hv
    change (a v).1 = _
    rw [← ha (subset_convexHull ℝ _ hv), hgv v hvK]
    split_ifs <;> rfl
  have hAx : A x = 0 := by
    change (a x).1 = 0
    rw [← ha hxt]
    exact he.symm
  have hxzero := t.mem_convexHull_zero_vertices A
    (fun v hv => by rw [hAv v hv]; split_ifs <;> norm_num) hxt hAx
  apply hxoff
  apply convexHull_subset_affineSpan _ (convexHull_mono (t := (s : Set E)) ?_ hxzero)
  intro v hv
  by_contra hvs
  change v ∉ s at hvs
  have hvzero : A v = 0 := hv.2
  rw [hAv v hv.1, if_neg hvs] at hvzero
  exact one_ne_zero hvzero

theorem AffineOnFaces.graph_off_face_normalized_mem_link (hg : K.AffineOnFaces g)
    (hgv : ∀ v ∈ K.vertices, g v = if v ∈ s then 0 else (1, v))
    {x : E} (hx : x ∈ (K.closedFaceStar s).space)
    (hxoff : x ∉ affineSpan ℝ (s : Set E)) :
    (g x).1⁻¹ • (g x).2 ∈ (K.faceLink s).space := by
  classical
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
  have hxK : x ∈ K.space := K.convexHull_subset_space ht.1 hxt
  have hpos := hg.graph_off_face_pos hgv hxK hxoff
  let b : E →ᴬ[ℝ] ℝ × E :=
    (ContinuousAffineMap.const ℝ E (1 : ℝ)).prod (ContinuousAffineMap.id ℝ E)
  have hverts : g '' (t : Set E) ⊆ insert 0 (b '' ((t \ s : Finset E) : Set E)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvK : v ∈ K.vertices := by rw [vertices_eq]; exact mem_biUnion ht.1 hv
    rw [hgv v hvK]
    by_cases hvs : v ∈ s
    · simp only [if_pos hvs]
      exact mem_insert 0 _
    · rw [if_neg hvs]
      exact mem_insert_of_mem _ ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvs⟩, rfl⟩
  have hgcone : g x ∈ convexHull ℝ (insert 0 (b '' ((t \ s : Finset E) : Set E))) := by
    apply convexHull_mono hverts
    rw [← hg.image_convexHull ht.1]
    exact ⟨x, hxt, rfl⟩
  have hgzero : g x ≠ 0 := by
    intro he
    simp only [he, Prod.fst_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  obtain ⟨y, hy, r, hr, hgr⟩ := exists_pos_smul_of_mem_convexHull_insert_zero hgcone hgzero
  change y ∈ convexHull ℝ (b.toAffineMap '' ((t \ s : Finset E) : Set E)) at hy
  rw [← b.toAffineMap.image_convexHull] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  change g x = r • (1, z) at hgr
  have hfst : (g x).1 = r := by
    simpa only [Prod.smul_fst, smul_eq_mul, mul_one] using congrArg Prod.fst hgr
  have hsnd : (g x).2 = r • z := congrArg Prod.snd hgr
  rw [hfst, hsnd, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
  rcases K.sdiff_mem_faceLink_or_empty s ht with he | hface
  · simp only [he, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hz
  · exact convexHull_subset_space hface hz

end Geometry.SimplicialComplex

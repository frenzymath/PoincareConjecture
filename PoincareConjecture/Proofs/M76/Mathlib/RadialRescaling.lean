import PoincareConjecture.Proofs.M76.Mathlib.RadialConvexHull
import PoincareConjecture.Proofs.M76.Mathlib.RadialStar











set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem LinearIndependent.image_smul_of_ne_zero {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) (r : E → ℝ)
    (hr : ∀ x ∈ s, r x ≠ 0) :
    LinearIndependent ℝ ((↑) : ((fun x => r x • x) '' s) → E) := by
  have h := hs.units_smul (fun x : s => Units.mk0 (r x) (hr x x.property))
  have hi : LinearIndependent ℝ (fun x : s => r x • (x : E)) := h
  change LinearIndepOn ℝ id ((fun x => r x • x) '' s)
  rw [Set.image_eq_range]
  exact hi.linearIndepOn_id

namespace Geometry.SimplicialComplex

variable {K : SimplicialComplex ℝ E}



theorem face_subset_vertices {s : Finset E} (hs : s ∈ K.faces) :
    (s : Set E) ⊆ K.vertices := by
  rw [vertices_eq]
  exact subset_biUnion_of_mem hs

private theorem radial_rescale_common_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) {z w : E}
    (hz : z ∈ convexHull ℝ ((fun x => r x • x) '' (s : Set E)))
    (hw : w ∈ convexHull ℝ ((fun x => r x • x) '' (t : Set E)))
    (hzw : NormedSpace.normalize z = NormedSpace.normalize w) :
    z = w ∧ z ∈ convexHull ℝ ((fun x => r x • x) '' ((s : Set E) ∩ t)) := by
  have hrs : ∀ x ∈ (s : Set E), 0 < r x := fun x hx => hr x (face_subset_vertices hs hx)
  have hrt : ∀ x ∈ (t : Set E), 0 < r x := fun x hx => hr x (face_subset_vertices ht hx)
  have hsnorm := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r hrs
  have htnorm := normalize_image_convexHull_pos_smul (hlin t ht).zero_notMem_convexHull r hrt
  obtain ⟨x, hxs, hxz⟩ := hsnorm.subset ⟨z, hz, rfl⟩
  obtain ⟨y, hyt, hyw⟩ := htnorm.subset ⟨w, hw, rfl⟩
  have hxy := hinj (convexHull_subset_space hs hxs) (convexHull_subset_space ht hyt)
    (hxz.trans (hzw.trans hyw.symm))
  have hxinter : x ∈ convexHull ℝ ((s : Set E) ∩ t) :=
    K.inter_subset_convexHull hs ht ⟨hxs, hxy ▸ hyt⟩
  have hzero : (0 : E) ∉ convexHull ℝ ((s : Set E) ∩ t) :=
    fun h => (hlin s hs).zero_notMem_convexHull (convexHull_mono inter_subset_left h)
  have hinter := normalize_image_convexHull_pos_smul hzero r (fun x hx => hrs x hx.1)
  obtain ⟨p, hp, hpx⟩ := hinter.symm.subset ⟨x, hxinter, rfl⟩
  have hps : p ∈ convexHull ℝ ((fun x => r x • x) '' (s : Set E)) :=
    convexHull_mono (image_mono inter_subset_left) hp
  have hpt : p ∈ convexHull ℝ ((fun x => r x • x) '' (t : Set E)) :=
    convexHull_mono (image_mono inter_subset_right) hp
  have hsind := (hlin s hs).image_smul_of_ne_zero r (fun x hx => (hrs x hx).ne')
  have htind := (hlin t ht).image_smul_of_ne_zero r (fun x hx => (hrt x hx).ne')
  have hpz := hsind.injOn_normalize_convexHull hps hz (hpx.trans hxz)
  have hpw := htind.injOn_normalize_convexHull hpt hw (hpx.trans (hxz.trans hzw))
  exact ⟨hpz.symm.trans hpw, hpz ▸ hp⟩

variable [DecidableEq E]




def radialRescale (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) : SimplicialComplex ℝ E where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map (fun x => r x • x)
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    have h := (hlin s hs).image_smul_of_ne_zero r
      (fun x hx => (hr x (face_subset_vertices hs hx)).ne')
    rw [← Finset.coe_image] at h
    exact h.affineIndependent
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ z ⟨hz, hzt⟩
    simp only [Finset.coe_image] at hz hzt ⊢
    exact convexHull_mono (Set.image_inter_subset _ _ _)
      (radial_rescale_common_face hlin hinj r hr hs ht hz hzt rfl).2



theorem radialRescale_faces (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).faces =
      (fun s : Finset E => s.image (fun x => r x • x)) '' K.faces := rfl



theorem finite_radialRescale_faces (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).faces.Finite := hK.image _



theorem linearIndependent_radialRescale_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    {s : Finset E} (hs : s ∈ (K.radialRescale hlin hinj r hr).faces) :
    LinearIndependent ℝ ((↑) : s → E) := by
  obtain ⟨t, ht, rfl⟩ := hs
  have h := (hlin t ht).image_smul_of_ne_zero r
    (fun x hx => (hr x (face_subset_vertices ht hx)).ne')
  rwa [← Finset.coe_image] at h



theorem injOn_normalize_radialRescale
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    InjOn (NormedSpace.normalize : E → E) (K.radialRescale hlin hinj r hr).space := by
  intro z hz w hw hzw
  obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_space_iff.mp hz
  obtain ⟨_, ⟨t, ht, rfl⟩, hwt⟩ := mem_space_iff.mp hw
  simp only [Finset.coe_image] at hzs hwt
  exact (radial_rescale_common_face hlin hinj r hr hs ht hzs hwt hzw).1



theorem normalize_image_radialRescale_space
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    NormedSpace.normalize '' (K.radialRescale hlin hinj r hr).space =
      NormedSpace.normalize '' K.space := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_space_iff.mp hz
    rw [Finset.coe_image] at hzs
    have h := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r
      (fun x hx => hr x (face_subset_vertices hs hx))
    obtain ⟨x, hx, he⟩ := h.subset ⟨z, hzs, rfl⟩
    exact ⟨x, convexHull_subset_space hs hx, he⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    have h := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r
      (fun x hx => hr x (face_subset_vertices hs hx))
    obtain ⟨z, hz, he⟩ := h.symm.subset ⟨x, hxs, rfl⟩
    refine ⟨z, convexHull_subset_space (K := K.radialRescale hlin hinj r hr)
      (show s.image (fun x => r x • x) ∈ _ from ⟨s, hs, rfl⟩) ?_, he⟩
    simpa only [Finset.coe_image] using hz

end Geometry.SimplicialComplex

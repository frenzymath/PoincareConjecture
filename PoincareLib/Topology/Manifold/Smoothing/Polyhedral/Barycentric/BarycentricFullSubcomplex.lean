import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricStarFaces

/-!
# Fullness of barycentrically subdivided subcomplexes

The centroid of a coarse face retains its exact face label.
Consequently subdivision preserves subcomplex inclusion and
makes every subcomplex full. These are the face-chain inputs
for a finite polyhedron neighborhood retraction. See Hudson
1969, pp. 8--9, 15--19 and M76 derivation 270.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [Fintype K.faces] in
/-- Centroids retain the exact nonempty face of a finite
complex. See Hudson pp. 8--9 and M76 derivation 270. -/
theorem faceCentroid_injective [Finite K.faces] :
    Function.Injective (fun s : K.faces => s.val.centroid ℝ id) := by
  apply K.positiveFaceCenter_injective
  intro s
  have hs := K.nonempty_of_mem_faces s.property
  refine ⟨s.val.centroidWeights ℝ, ?_,
    s.val.sum_centroidWeights_eq_one_of_nonempty ℝ hs, ?_⟩
  · intro v _
    simp only [Finset.centroidWeights_apply, inv_pos]
    exact_mod_cast hs.card_pos
  · rw [Finset.centroid_eq_inv_card_smul_sum _ hs]
    simp only [Finset.centroidWeights_apply, Finset.smul_sum, id_eq]

/-- Barycentric faces are centroid images of chains of actual
coarse finite vertex sets. See Hudson pp. 8--9 and M76
derivation 270. -/
theorem barycentricSubdivision_faces_of_face_chains [DecidableEq E] (t : Finset E) :
    t ∈ K.barycentricSubdivision.faces ↔
      ∃ a : Finset (Finset E), a.Nonempty ∧ (∀ s ∈ a, s ∈ K.faces) ∧
        (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧
        t = a.image (fun s => s.centroid ℝ id) := by
  classical
  rw [K.barycentricSubdivision_faces]
  constructor
  · rintro ⟨a, ha, hchain, rfl⟩
    refine ⟨a.image Subtype.val, ha.image _, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact i.property
    · intro s hs u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      exact hchain i hi j hj
    · rw [Finset.image_image]
      rfl
  · rintro ⟨a, ha, hfaces, hchain, rfl⟩
    let v : a → K.faces := fun s => ⟨s.val, hfaces s.val s.property⟩
    refine ⟨a.attach.image v, ha.attach.image v, ?_, ?_⟩
    · intro i hi j hj
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
      exact hchain s.val s.property u.val u.property
    · rw [Finset.image_image]
      change a.image (fun s => s.centroid ℝ id) =
        a.attach.image ((fun s => s.centroid ℝ id) ∘ ((↑) : a → Finset E))
      rw [← Finset.image_image, Finset.attach_image_val]

/-- Barycentric subdivision preserves inclusion of the actual
finite subcomplexes. See Hudson pp. 8--9 and M76 derivation 270. -/
theorem barycentricSubdivision_mono {L : SimplicialComplex ℝ E} [Fintype L.faces]
    (hKL : K ≤ L) : K.barycentricSubdivision ≤ L.barycentricSubdivision := by
  classical
  intro t ht
  obtain ⟨a, ha, hfaces, hchain, rfl⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains t).mp ht
  exact (L.barycentricSubdivision_faces_of_face_chains _).mpr
    ⟨a, ha, fun s hs => hKL (hfaces s hs), hchain, rfl⟩

/-- The vertices of the barycentric subdivision are exactly
the centroids of its original nonempty faces. See Hudson
pp. 8--9 and M76 derivation 270. -/
theorem mem_barycentricSubdivision_vertices_iff (x : E) :
    x ∈ K.barycentricSubdivision.vertices ↔
      ∃ s ∈ K.faces, s.centroid ℝ id = x := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, hfaces, _, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains {x}).mp hx
    obtain ⟨s, hs⟩ := ha
    refine ⟨s, hfaces s hs, ?_⟩
    apply Finset.mem_singleton.mp
    rw [heq]
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
    refine ⟨{s}, Finset.singleton_nonempty s, ?_, ?_, ?_⟩
    · intro u hu
      simpa only [Finset.mem_singleton.mp hu] using hs
    · intro u hu v hv
      have hu' := Finset.mem_singleton.mp hu
      have hv' := Finset.mem_singleton.mp hv
      subst u
      subst v
      exact Or.inl Subset.rfl
    · rw [Finset.image_singleton]

omit [Fintype K.faces] in
/-- A coarse face centroid is a vertex of the subdivided
subcomplex exactly when that same original face belongs to
the subcomplex. See Hudson pp. 8--9 and M76 derivation 270. -/
theorem faceCentroid_mem_barycentricSubdivision_iff [Finite K.faces]
    {L : SimplicialComplex ℝ E} [Fintype L.faces] (hLK : L ≤ K)
    (s : K.faces) :
    s.val.centroid ℝ id ∈ L.barycentricSubdivision.vertices ↔ s.val ∈ L.faces := by
  constructor
  · intro hx
    obtain ⟨t, ht, hts⟩ := (L.mem_barycentricSubdivision_vertices_iff _).mp hx
    have heq : (⟨t, hLK ht⟩ : K.faces) = s := K.faceCentroid_injective hts
    exact congrArg Subtype.val heq ▸ ht
  · intro hs
    exact (L.mem_barycentricSubdivision_vertices_iff _).mpr ⟨s.val, hs, rfl⟩

/-- Every face of the barycentric subdivision whose vertices
belong to the subdivided subcomplex is itself in that
subcomplex. See Hudson pp. 8--9 and M76 derivation 270. -/
theorem barycentricSubdivision_full {L : SimplicialComplex ℝ E} [Fintype L.faces]
    (hLK : L ≤ K) {t : Finset E} (ht : t ∈ K.barycentricSubdivision.faces)
    (hverts : ∀ v ∈ t, v ∈ L.barycentricSubdivision.vertices) :
    t ∈ L.barycentricSubdivision.faces := by
  classical
  obtain ⟨a, ha, hfaces, hchain, rfl⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains t).mp ht
  apply (L.barycentricSubdivision_faces_of_face_chains _).mpr
  refine ⟨a, ha, ?_, hchain, rfl⟩
  intro s hs
  apply (K.faceCentroid_mem_barycentricSubdivision_iff hLK ⟨s, hfaces s hs⟩).mp
  exact hverts _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

end Geometry.SimplicialComplex

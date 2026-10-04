import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.RadialEmbeddingSpace

/-!
# General-position geometric realizations

Independent position vectors realize every abstract simplicial complex
on their labels faithfully and radially. This is the general-position
source of Cairns 1940, Section 3, pp. 798--799, and Lemma 5.1,
p. 801. See M76 derivation 26.
-/

set_option autoImplicit false

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ι → E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem image_face_subset_range {A : AbstractSimplicialComplex ι}
    [DecidableEq E] {t : Finset E}
    (ht : t ∈ (A.toPreAbstractSimplicialComplex.map v).faces) :
    (t : Set E) ⊆ range v := by
  obtain ⟨s, _, rfl⟩ := ht
  simpa only [Finset.coe_image] using image_subset_range v s

/-- The geometric realization whose vertices are an independent
family, with exactly the prescribed labelled faces.
See Cairns pp. 798--799 and M76 derivation 26. -/
noncomputable def independentComplex (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) : SimplicialComplex ℝ E := by
  classical
  refine { A.toPreAbstractSimplicialComplex.map v with
    indep := fun hs => (hv.linearIndepOn_id.mono (image_face_subset_range hs)).affineIndependent
    inter_subset_convexHull := ?_ }
  intro s t hs ht
  have hsub : ((s ∪ t : Finset E) : Set E) ⊆ range v := by
    simpa only [Finset.coe_union] using
      union_subset (image_face_subset_range hs) (image_face_subset_range ht)
  exact ((hv.linearIndepOn_id.mono hsub).affineIndependent.convexHull_inter').symm.subset

/-- Faces of the independent realization are precisely the labelled
abstract faces. See Cairns p. 799 and M76 derivation 26. -/
theorem independentComplex_faces (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) :
    (A.independentComplex hv).faces =
      {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} := by
  classical
  ext t
  change (∃ s ∈ A.faces, s.image v = t) ↔ _
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Finset.coe_image⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Finset.coe_injective (Finset.coe_image.trans he.symm)⟩

/-- Every abstract complex has a faithful radial realization on any
linearly independent assignment of position vectors.
See Cairns pp. 798--799 and M76 derivation 26. -/
theorem isRadialEmbedding_of_linearIndependent (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) : A.IsRadialEmbedding v := by
  classical
  refine ⟨hv.injective, A.independentComplex hv, A.independentComplex_faces hv,
    fun _ ht => hv.linearIndepOn_id.mono (image_face_subset_range ht), ?_⟩
  apply hv.linearIndepOn_id.injOn_normalize_convexHull.mono
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact convexHull_mono (image_face_subset_range hs) hxs

end AbstractSimplicialComplex

import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSuperlevelDeformation
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricRealization
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex












set_option autoImplicit false

open Set StdSimplexCore

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem vertexSubcomplex_eq_of_full
    {K L : SimplicialComplex ℝ E} (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) :
    K.vertexSubcomplex L.vertices = L := by
  apply le_antisymm
  · intro s hs
    exact hfull s hs.1 hs.2
  · exact le_vertexSubcomplex hLK Subset.rfl

open scoped Classical in




theorem image_barycentric_vertexSubcomplex
    (K : SimplicialComplex ℝ E) [Fintype K.vertices] (V : Set E) :
    let s := Finset.univ.filter (fun v : K.vertices => (v : E) ∈ V)
    barycentricMap ((↑) : K.vertices → E) ''
      (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace ∩
        barycentricFace s) = (K.vertexSubcomplex V).space := by
  classical
  let s := Finset.univ.filter (fun v : K.vertices => (v : E) ∈ V)
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  change barycentricMap ((↑) : K.vertices → E) ''
    (A.barycentricSpace ∩ barycentricFace s) = (K.vertexSubcomplex V).space
  apply Subset.antisymm
  · rintro _ ⟨q, ⟨hqA, hqs⟩, rfl⟩
    obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hqA
    let r := t ∩ s
    have hqr : q ∈ barycentricFace r := by
      refine ⟨hqt.1, ?_⟩
      intro i hi
      by_cases hit : i ∈ t
      · exact hqs.2 i (fun his => hi (Finset.mem_inter.mpr ⟨hit, his⟩))
      · exact hqt.2 i hit
    have hrne : r.Nonempty := by
      by_contra h
      have hrempty := Finset.not_nonempty_iff_eq_empty.mp h
      have hsum := sum_eq_one_of_mem_barycentricFace hqr
      simp only [hrempty, Finset.sum_empty] at hsum
      exact zero_ne_one hsum
    have hrA : r ∈ A.faces :=
      (A.isRelLowerSet_faces ht).2 Finset.inter_subset_left hrne
    let u := r.map (Function.Embedding.subtype (fun x => x ∈ K.vertices))
    have hu : u ∈ (K.vertexSubcomplex V).faces := by
      refine ⟨hrA, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
    apply (K.vertexSubcomplex V).convexHull_subset_space hu
    rw [Finset.coe_map, Function.Embedding.coe_subtype, ← image_barycentricFace]
    exact mem_image_of_mem _ hqr
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨u, hu, he⟩ := K.faces_eq_vertexAbstractComplex_images ▸ ht.1
    have hus : u ⊆ s := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      apply ht.2 i.val
      change (i : E) ∈ (t : Set E)
      rw [he]
      exact mem_image_of_mem Subtype.val hi
    rw [he, ← image_barycentricFace ((↑) : K.vertices → E) u] at hxt
    obtain ⟨q, hqu, hqx⟩ := hxt
    exact ⟨q, ⟨mem_iUnion₂.mpr ⟨u, hu, hqu⟩,
      ⟨hqu.1, fun i hi => hqu.2 i (fun hiu => hi (hus hiu))⟩⟩, hqx⟩

end Geometry.SimplicialComplex

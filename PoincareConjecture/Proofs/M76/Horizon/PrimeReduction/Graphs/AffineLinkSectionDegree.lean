import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.LinkSectionDegree
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence









set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_two_segment_germ_of_affine_link_section_ncard
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) (A : E →ᵃ[ℝ] ℝ) (hpA : A p = 0)
    (hcount : ((K.link p).space ∩ {x | A x = 0}).ncard = 2) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      segment ℝ p u ∩ segment ℝ p v ⊆ {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ K.space ∩ {y | A y = 0} ↔
        x ∈ segment ℝ p u ∪ segment ℝ p v := by
  let e : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hep : e p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hheight (x : E) : A.linear (e x) = A x := by
    change A.linear (-p + x) = A x
    have h : A.linear (-p + x) = A x - A p := by
      simpa only [vsub_eq_sub, sub_eq_add_neg, add_comm] using A.linearMap_vsub x p
    simpa only [hpA, sub_zero] using h
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let R := hf.embeddedImage e.injective.injOn
  have hR : R.faces.Finite := hf.embeddedImage_finite e.injective.injOn hK
  have hRs : R.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have hRzero : (0 : E) ∈ R.vertices := by
    rw [hf.embeddedImage_vertices e.injective.injOn]
    exact ⟨p, hp, hep⟩
  have hRlink : (R.link 0).space = e '' (K.link p).space := by
    have h := hf.embeddedImage_link_space e.injective.injOn hp
    change (R.link (e p)).space = e '' (K.link p).space at h
    simpa only [hep] using h
  have hsection : (R.link 0).space ∩ {x | A.linear x = 0} =
      e '' ((K.link p).space ∩ {x | A x = 0}) := by
    rw [hRlink]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzA⟩
      exact ⟨z, ⟨hz, (hheight z).symm.trans hzA⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzA⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hheight z).trans hzA⟩
  have hcountR : ((R.link 0).space ∩ {x | A.linear x = 0}).ncard = 2 := by
    rw [hsection, Set.ncard_image_of_injective _ e.injective]
    exact hcount
  obtain ⟨u, v, hu, hv, hinter, hlocal⟩ :=
    R.exists_two_segment_germ_of_link_section_ncard hR hRzero A.linear hcountR
  have hseg (w : E) : e '' segment ℝ p (e.symm w) = segment ℝ 0 w := by
    have h := image_segment ℝ e.toAffineEquiv.toAffineMap p (e.symm w)
    change e '' segment ℝ p (e.symm w) = segment ℝ (e p) (e (e.symm w)) at h
    simpa only [hep, e.apply_symm_apply] using h
  have hmem (S : Set E) (x : E) : e x ∈ e '' S ↔ x ∈ S := e.injective.mem_set_image
  refine ⟨e.symm u, e.symm v, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hu ((e.apply_symm_apply u).symm.trans ((congrArg e h).trans hep))
  · intro h
    exact hv ((e.apply_symm_apply v).symm.trans ((congrArg e h).trans hep))
  · intro x hx
    have hu' : e x ∈ segment ℝ 0 u := (hseg u).subset (mem_image_of_mem e hx.1)
    have hv' : e x ∈ segment ℝ 0 v := (hseg v).subset (mem_image_of_mem e hx.2)
    exact e.injective ((hinter ⟨hu', hv'⟩).trans hep.symm)
  · have hc : Tendsto e (𝓝 p) (𝓝 0) := by
      simpa only [hep] using e.continuous.tendsto p
    filter_upwards [hc.eventually hlocal] with x hx
    rw [hRs, ← hseg u, ← hseg v, mem_union, hmem, hmem,
      mem_inter_iff, hmem, mem_ofPred_eq, hheight] at hx
    exact hx



theorem ncard_graph_degree_of_affine_link_section_ncard
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    {p : E} (hpK : p ∈ K.vertices) (hpG : p ∈ G.vertices)
    (hbound : ∀ a ∈ G.faces, a.card ≤ 2) (A : E →ᵃ[ℝ] ℝ) (hpA : A p = 0)
    (hcount : ((K.link p).space ∩ {x | A x = 0}).ncard = 2)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ G.space ↔ x ∈ K.space ∩ {y | A y = 0}) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpG⟩).ncard = 2 := by
  obtain ⟨u, v, hu, hv, hinter, hsection⟩ :=
    K.exists_two_segment_germ_of_affine_link_section_ncard hK hpK A hpA hcount
  apply G.ncard_neighborSet_eq_two_of_local_segments hG hbound hpG hu hv hinter
  filter_upwards [hlocal, hsection] with x hx hs
  exact hx.trans hs

end Geometry.SimplicialComplex

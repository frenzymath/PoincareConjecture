import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence

set_option autoImplicit false

open Set Metric Geometry Topology Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in

theorem face_card_and_degree_of_two_segment_germs
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hgerms : ∀ x ∈ G.space, ∃ u v : E, u ≠ x ∧ v ≠ x ∧
      segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
      ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ segment ℝ x u ∪ segment ℝ x v) :
    (∀ a ∈ G.faces, a.card ≤ 2) ∧
      ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
  classical
  have hlocal : ∀ x : G.space, ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧
      ∃ F : Finset (AffineSubspace ℝ E),
        (∀ A ∈ F, Module.finrank ℝ A.direction ≤ 1) ∧
          ∀ z ∈ G.space ∩ U, ∃ A ∈ F, z ∈ A := by
    intro x
    obtain ⟨u, v, _hu, _hv, _hinter, hnear⟩ := hgerms x x.property
    obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hnear
    refine ⟨U, hU, hxU, {affineSpan ℝ ({(x : E), u} : Set E),
      affineSpan ℝ ({(x : E), v} : Set E)}, ?_, ?_⟩
    · intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl <;> rw [direction_affineSpan]
      · exact (collinear_pair ℝ (x : E) u).finrank_le_one
      · exact (collinear_pair ℝ (x : E) v).finrank_le_one
    · intro z hz
      rcases (hUsub hz.2).mp hz.1 with hzu | hzv
      · exact ⟨_, Finset.mem_insert_self _ _,
          convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hzu)⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hzv)⟩
  choose U hU hxU F hFdim hFcover using hlocal
  obtain ⟨I, hI⟩ := (G.isCompact_space_of_finite hG).elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let cover := I.biUnion F
  have hdim : ∀ A ∈ cover, Module.finrank ℝ A.direction ≤ 1 := by
    intro A hA
    obtain ⟨x, _hx, hAF⟩ := Finset.mem_biUnion.mp hA
    exact hFdim x A hAF
  have hcover : ∀ x ∈ G.space, ∃ A ∈ cover, x ∈ A := by
    intro x hx
    obtain ⟨z, hzI, hxU⟩ := mem_iUnion₂.mp (hI hx)
    obtain ⟨A, hA, hxA⟩ := hFcover z x ⟨hx, hxU⟩
    exact ⟨A, Finset.mem_biUnion.mpr ⟨z, hzI, hA⟩, hxA⟩
  have hcard : ∀ a ∈ G.faces, a.card ≤ 2 :=
    fun _ ha => G.face_card_le_of_finite_affine_cover cover hdim hcover ha
  have hlinkspace (v : G.vertices) : (G.link (v : E)).space =
      (G.faceLink {(v : E)}).vertices := by
    rw [← G.faceLink_singleton_eq_link]
    apply subset_antisymm
    · intro z hz
      obtain ⟨a, ha, hza⟩ := SimplicialComplex.mem_space_iff.mp hz
      have hbound := G.card_add_card_le_of_mem_faceLink hcard {(v : E)} ha
      have hpos := Finset.card_pos.mpr ((G.faceLink {(v : E)}).nonempty_of_mem_faces ha)
      simp only [Finset.card_singleton] at hbound
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show a.card = 1 by omega)
      have hza' : z = a := by
        simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hza
      exact hza'.symm ▸ ha
    · exact (G.faceLink {(v : E)}).vertices_subset_space
  have hdegree (v : G.vertices) :
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
    obtain ⟨u, w, hu, hw, hinter, hnear⟩ :=
      hgerms v (G.vertices_subset_space v.property)
    let e : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-(v : E))
    have he0 : e v = 0 := by change -(v : E) + v = 0; exact neg_add_cancel _
    have hei0 : e.symm 0 = (v : E) := e.injective (by rw [e.apply_symm_apply, he0])
    let hf := G.affineOnFaces_affine e.toContinuousAffineMap
    let J := hf.embeddedImage e.injective.injOn
    have hJ := hf.embeddedImage_finite e.injective.injOn hG
    have hJs : J.space = e '' G.space := hf.embeddedImage_space e.injective.injOn
    have hJv : (0 : E) ∈ J.vertices := by
      rw [hf.embeddedImage_vertices e.injective.injOn]
      exact ⟨v, v.property, he0⟩
    have hJl : (J.link 0).space = e '' (G.link (v : E)).space := by
      have h := hf.embeddedImage_link_space e.injective.injOn v.property
      change (J.link (e v)).space = e '' (G.link (v : E)).space at h
      simpa only [he0] using h
    have hcount : (J.link 0).space.ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard := by
      rw [hJl, ncard_image_of_injective _ e.injective, hlinkspace,
        G.ncard_edgeGraph_neighborSet]
    have hseg (a : E) : e '' segment ℝ (v : E) a = segment ℝ 0 (e a) := by
      have h := image_segment ℝ e.toAffineEquiv.toAffineMap (v : E) a
      change e '' segment ℝ (v : E) a = segment ℝ (e v) (e a) at h
      simpa only [he0] using h
    have hpre (S : Set E) (z : E) : e.symm z ∈ S ↔ z ∈ e '' S := by
      constructor
      · intro hz
        exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
      · rintro ⟨a, ha, rfl⟩
        simpa only [e.symm_apply_apply] using ha
    have hnearJ : ∀ᶠ z in 𝓝 (0 : E),
        z ∈ J.space ∩ {a | (0 : E →ₗ[ℝ] ℝ) a = 0} ↔
          z ∈ segment ℝ 0 (e u) ∪ segment ℝ 0 (e w) := by
      have htend : Tendsto e.symm (𝓝 (0 : E)) (𝓝 (v : E)) := by
        simpa only [hei0] using e.symm.continuous.tendsto 0
      have h := htend.eventually hnear
      filter_upwards [h] with z hz
      simp only [LinearMap.zero_apply, Set.ofPred_true, inter_univ]
      rw [hJs, ← hseg u, ← hseg w, ← image_union, ← hpre, ← hpre]
      exact hz
    have heu : e u ≠ 0 := fun h => hu (e.injective (h.trans he0.symm))
    have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans he0.symm))
    rw [← hcount]
    have hinterJ : segment ℝ 0 (e u) ∩ segment ℝ 0 (e w) ⊆ {0} := by
      rw [← hseg u, ← hseg w, ← image_inter e.injective]
      rintro z ⟨a, ha, rfl⟩
      exact (congrArg e (hinter ha)).trans he0
    simpa only [LinearMap.zero_apply, Set.ofPred_true, inter_univ] using
      J.ncard_link_zero_of_local_segments hJ hJv (0 : E →ₗ[ℝ] ℝ)
        heu hew hinterJ hnearJ
  exact ⟨hcard, hdegree⟩

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.GraphIncidence
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors



set_option autoImplicit false
open Set Metric Geometry Topology Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem face_card_and_degree_of_boundary_segment_germs
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite) (Q : Set E)
    (hgerms : ∀ x ∈ G.space, ∃ u v : E, u ≠ x ∧ v ≠ x ∧
      (x ∈ Q → u = v) ∧
      (x ∉ Q → segment ℝ x u ∩ segment ℝ x v ⊆ {x}) ∧
      ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ segment ℝ x u ∪ segment ℝ x v) :
    (∀ a ∈ G.faces, a.card ≤ 2) ∧
    (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      if (v : E) ∈ Q then 1 else 2) ∧
    G.space ∩ Q = Subtype.val '' {v : G.vertices |
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  classical
  have hlocal (x : G.space) : ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧
      ∃ F : Finset (AffineSubspace ℝ E),
        (∀ A ∈ F, Module.finrank ℝ A.direction ≤ 1) ∧
        ∀ z ∈ G.space ∩ U, ∃ A ∈ F, z ∈ A := by
    obtain ⟨u, v, _hu, _hv, _hboundary, _hinter, hnear⟩ := hgerms x x.property
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
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : E) ∈ Q then 1 else 2 := by
    obtain ⟨u, w, hu, hw, hboundary, hinter, hnear⟩ :=
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
    by_cases hvR : (v : E) ∈ Q
    · rw [if_pos hvR, ← hcount]
      have hn := J.normalize_image_link_zero_of_local_segments hJ hJv
        (0 : E →ₗ[ℝ] ℝ) heu hew hnearJ
      simp only [LinearMap.zero_apply, Set.ofPred_true, inter_univ, hboundary hvR,
        Set.pair_eq_singleton] at hn
      rw [← J.injOn_normalize_link.ncard_image, hn, ncard_singleton]
    · rw [if_neg hvR, ← hcount]
      have hinterJ : segment ℝ 0 (e u) ∩ segment ℝ 0 (e w) ⊆ {0} := by
        rw [← hseg u, ← hseg w, ← image_inter e.injective]
        rintro z ⟨a, ha, rfl⟩
        exact (congrArg e (hinter hvR ha)).trans he0
      simpa only [LinearMap.zero_apply, Set.ofPred_true, inter_univ] using
        J.ncard_link_zero_of_local_segments hJ hJv (0 : E →ₗ[ℝ] ℝ)
          heu hew hinterJ hnearJ
  have hrimvertex : G.space ∩ Q ⊆ G.vertices := by
    intro x hx
    by_contra hxv
    obtain ⟨a, ha, hxa⟩ := G.exists_face_intrinsicInterior_of_finite hG hx.1
    have ha2 : a.card = 2 := by
      have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces ha)
      have hbound := hcard a ha
      by_contra hn
      have hone : a.card = 1 := by omega
      obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hone
      have hxq : x = q := by
        simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff]
          using intrinsicInterior_subset hxa
      exact hxv (hxq.symm ▸ ha)
    have hmax : ∀ b ∈ G.faces, a ⊆ b → b = a := by
      intro b hb hab
      exact (Finset.eq_of_subset_of_card_le hab (by rw [ha2]; exact hcard b hb)).symm
    obtain ⟨U, hU, hxU, hUg⟩ := G.exists_open_maximal_face_affine_germ hG ha hmax hxa
    obtain ⟨u, v, hu, _hv, hboundary, _hinter, hnear⟩ := hgerms x hx.1
    rw [← hboundary hx.2, union_self] at hnear
    obtain ⟨q, hqa⟩ := G.nonempty_of_mem_faces ha
    have hqx : q ≠ x := fun h => hxv (h ▸ G.face_subset_vertices ha hqa)
    have hxspan : x ∈ affineSpan ℝ (a : Set E) :=
      convexHull_subset_affineSpan _ (intrinsicInterior_subset hxa)
    have hqspan : q ∈ affineSpan ℝ (a : Set E) := subset_affineSpan ℝ _ hqa
    let A : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap x q
    have hA0 : A 0 = x := AffineMap.lineMap_apply_zero _ _
    have hn : {r : ℝ | A r ∈ U ∧ (A r ∈ G.space ↔ A r ∈ segment ℝ x u) ∧
        A (-r) ∈ U ∧ (A (-r) ∈ G.space ↔ A (-r) ∈ segment ℝ x u)} ∈ 𝓝 0 := by
      have hnearU : ∀ᶠ z in 𝓝 x, z ∈ U ∧
          (z ∈ G.space ↔ z ∈ segment ℝ x u) := by
        filter_upwards [hU.mem_nhds hxU, hnear] with z hzU hz
        exact ⟨hzU, hz⟩
      have hp : Tendsto A (𝓝 (0 : ℝ)) (𝓝 x) := by
        simpa only [hA0] using A.continuous.tendsto 0
      have hm : Tendsto (fun r : ℝ => A (-r)) (𝓝 0) (𝓝 x) := by
        change Tendsto (A ∘ fun r : ℝ => -r) (𝓝 0) (𝓝 x)
        exact hp.comp (by simpa only [neg_zero] using
          (continuous_neg : Continuous (fun r : ℝ => -r)).tendsto 0)
      filter_upwards [hp.eventually hnearU, hm.eventually hnearU] with r hr hr'
      exact ⟨hr.1, hr.2, hr'.1, hr'.2⟩
    obtain ⟨r, hr, hn⟩ := Set.exists_pos_smul_mem_of_mem_nhds hn (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at hn
    have hpseg := hn.2.1.mp ((hUg _ hn.1).mpr (AffineMap.lineMap_mem r hxspan hqspan))
    have hmseg := hn.2.2.2.mp ((hUg _ hn.2.2.1).mpr
      (AffineMap.lineMap_mem (-r) hxspan hqspan))
    obtain ⟨α, β, _hα, hβ, hab, heq⟩ := hpseg
    obtain ⟨γ, δ, _hγ, hδ, hgd, heq'⟩ := hmseg
    have hp : β • (u - x) = r • (q - x) := by
      change α • x + β • u = AffineMap.lineMap x q r at heq
      rw [AffineMap.lineMap_apply_module'] at heq
      rw [show α = 1 - β by linarith] at heq
      calc
        β • (u - x) = ((1 - β) • x + β • u) - x := by module
        _ = r • (q - x) := by rw [heq]; module
    have hm : δ • (u - x) = (-r) • (q - x) := by
      change γ • x + δ • u = AffineMap.lineMap x q (-r) at heq'
      rw [AffineMap.lineMap_apply_module'] at heq'
      rw [show γ = 1 - δ by linarith] at heq'
      calc
        δ • (u - x) = ((1 - δ) • x + δ • u) - x := by module
        _ = (-r) • (q - x) := by rw [heq']; module
    have hsum : (β + δ) • (u - x) = 0 := by rw [add_smul, hp, hm]; module
    have hcoef := (smul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr hu)
    have hβ0 : β = 0 := by linarith
    exact (smul_ne_zero hr.1.ne' (sub_ne_zero.mpr hqx))
      (by simpa only [hβ0, zero_smul] using hp.symm)
  refine ⟨hcard, hdegree, ?_⟩
  ext x
  constructor
  · intro hx
    let v : G.vertices := ⟨x, hrimvertex hx⟩
    refine ⟨v, ?_, rfl⟩
    change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1
    rw [hdegree, if_pos hx.2]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨G.vertices_subset_space v.property, ?_⟩
    by_contra hn
    change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 at hv
    rw [hdegree, if_neg hn] at hv
    omega

end Geometry.SimplicialComplex


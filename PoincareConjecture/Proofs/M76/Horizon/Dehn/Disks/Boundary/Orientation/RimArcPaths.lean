import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity
import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem exists_subcomplex_of_closed_vertex_partition
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (U V : Set E) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : U ∪ V = K.space) (hinter : U ∩ V ⊆ K.vertices) :
    ∃ L : SimplicialComplex ℝ E, L ≤ K ∧ L.space = U ∧
      ∀ x ∈ K.vertices, x ∈ L.vertices ↔ x ∈ U := by
  classical
  let L : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ U}
      indep := fun hs ↦ K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht ↦ K.inter_subset_convexHull hs.1 ht.1 }
  have hLK : L ≤ K := fun _ hs ↦ hs.1
  have hvertices (x : E) (hx : x ∈ K.vertices) : x ∈ L.vertices ↔ x ∈ U := by
    have hx' : {x} ∈ K.faces := hx
    change ({x} ∈ K.faces ∧ convexHull ℝ (({x} : Finset E) : Set E) ⊆ U) ↔ x ∈ U
    simp only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hx', true_and]
  have hLU : L.space ⊆ U := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  refine ⟨L, hLK, hLU.antisymm ?_, hvertices⟩
  intro x hxU
  by_cases hxv : x ∈ K.vertices
  · exact L.vertices_subset_space ((hvertices x hxv).mpr hxU)
  have hxK : x ∈ K.space := hcover ▸ Or.inl hxU
  obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  have hdis : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩ (U ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy, hyU, hyV⟩
    have hyv := hinter ⟨hyU, hyV⟩
    have hsy := K.subset_of_mem_intrinsicInterior_face hs hyv hy
      (by simp)
    have hxy : x = y := by
      have hx := convexHull_mono hsy (intrinsicInterior_subset hxs)
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hx
    exact hxv (hxy ▸ hyv)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior.isPreconnected U V hU hV
    (fun y hy ↦ hcover.symm ▸ K.convexHull_subset_space hs (intrinsicInterior_subset hy)) hdis
  have hinside : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ U :=
    hside.resolve_right (fun h ↦ hxv (hinter ⟨hxU, h hxs⟩))
  have hface : convexHull ℝ (s : Set E) ⊆ U :=
    (convex_convexHull ℝ (s : Set E)).subset_closure_intrinsicInterior.trans
      (closure_minimal hinside hU)
  exact SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hface⟩, intrinsicInterior_subset hxs⟩

theorem exists_edge_path_in_closed_vertex_partition
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (U V : Set E) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : U ∪ V = K.space) (hinter : U ∩ V ⊆ K.vertices)
    (hconn : IsPreconnected U) {a b : E}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices)
    (haU : a ∈ U) (hbU : b ∈ U) (hab : a ≠ b) :
    ∃ (n : ℕ) (p : ℕ → E), 0 < n ∧ p 0 = a ∧ p n = b ∧
      InjOn p (Icc 0 n) ∧ (∀ k ≤ n, p k ∈ U) ∧
      ∀ k < n, {p k, p (k + 1)} ∈ K.faces ∧
        convexHull ℝ ({p k, p (k + 1)} : Set E) ⊆ U := by
  obtain ⟨L, hLK, hLU, hvertices⟩ :=
    exists_subcomplex_of_closed_vertex_partition K hK U V hU hV hcover hinter
  let a' : L.vertices := ⟨a, (hvertices a ha).mpr haU⟩
  let b' : L.vertices := ⟨b, (hvertices b hb).mpr hbU⟩
  have hc := L.preconnected_edgeGraph_of_isPreconnected (hK.subset hLK) (hLU.symm ▸ hconn)
  obtain ⟨w, hw⟩ := (hc a' b').exists_isPath
  let p : ℕ → E := fun k ↦ w.getVert k
  have hn : 0 < w.length := by
    by_contra hn
    have hz : w.length = 0 := by omega
    have he := w.getVert_length
    rw [hz, w.getVert_zero] at he
    exact hab (congrArg Subtype.val he)
  refine ⟨w.length, p, hn, congrArg Subtype.val w.getVert_zero,
    congrArg Subtype.val w.getVert_length, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact hw.getVert_injOn hi.2 hj.2 (Subtype.ext hij)
  · intro k _
    exact hLU ▸ L.vertices_subset_space (w.getVert k).property
  · intro k hk
    have hadj := (w.adj_getVert_succ hk).2
    change ({w.getVert k, w.getVert (k + 1)} : Finset L.vertices).map
      (Function.Embedding.subtype _) ∈ L.faces at hadj
    simp only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] at hadj
    refine ⟨hLK hadj, ?_⟩
    intro x hx
    exact hLU ▸ L.convexHull_subset_space hadj (by simpa only [Finset.coe_pair] using hx)

theorem exists_edge_path_in_homeomorphic_rim_arc
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {W : Set E}
    (e : K.space ≃ₜ W) (U V : Set E) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : U ∪ V = W) (hconn : IsPreconnected U)
    {a b : E} (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b)
    (haU : (e ⟨a, K.vertices_subset_space ha⟩ : E) ∈ U)
    (hbU : (e ⟨b, K.vertices_subset_space hb⟩ : E) ∈ U)
    (hinter : U ∩ V ⊆
      {(e ⟨a, K.vertices_subset_space ha⟩ : E), (e ⟨b, K.vertices_subset_space hb⟩ : E)}) :
    ∃ (n : ℕ) (p : ℕ → E), 0 < n ∧ p 0 = a ∧ p n = b ∧
      InjOn p (Icc 0 n) ∧ (∀ k ≤ n, p k ∈ K.space) ∧
      ∀ k < n, {p k, p (k + 1)} ∈ K.faces ∧
        ∀ x : K.space, (x : E) ∈ convexHull ℝ ({p k, p (k + 1)} : Set E) →
          (e x : E) ∈ U := by
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let f : K.space → E := fun x ↦ e x
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  let U' := Subtype.val '' (f ⁻¹' U)
  let V' := Subtype.val '' (f ⁻¹' V)
  have hmem (S : Set E) (x : K.space) :
      (x : E) ∈ Subtype.val '' (f ⁻¹' S) ↔ f x ∈ S := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact Subtype.ext hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hU' : IsClosed U' :=
    ((hU.preimage hf).isCompact.image continuous_subtype_val).isClosed
  have hV' : IsClosed V' :=
    ((hV.preimage hf).isCompact.image continuous_subtype_val).isClosed
  have hcover' : U' ∪ V' = K.space := by
    ext x
    constructor
    · rintro (⟨y, _, rfl⟩ | ⟨y, _, rfl⟩) <;> exact y.property
    · intro hx
      have hy : f ⟨x, hx⟩ ∈ U ∪ V := hcover.symm ▸ (e ⟨x, hx⟩).property
      exact hy.elim (fun h ↦ Or.inl ((hmem U ⟨x, hx⟩).mpr h))
        (fun h ↦ Or.inr ((hmem V ⟨x, hx⟩).mpr h))
  have hinter' : U' ∩ V' ⊆ K.vertices := by
    rintro x ⟨hxU, hxV⟩
    obtain ⟨y, hy, rfl⟩ := hxU
    have h := hinter ⟨hy, (hmem V y).mp hxV⟩
    rcases h with h | h
    · have he := congrArg Subtype.val (e.injective (Subtype.ext h))
      exact he ▸ ha
    · have he := congrArg Subtype.val (e.injective (Subtype.ext h))
      exact he ▸ hb
  have himage : f '' (f ⁻¹' U) = U := by
    apply image_preimage_eq_of_subset
    intro y hy
    let y' : W := ⟨y, hcover ▸ Or.inl hy⟩
    exact ⟨e.symm y', congrArg Subtype.val (e.apply_symm_apply y')⟩
  have hconn' : IsPreconnected U' := by
    have hi : Topology.IsInducing f :=
      Topology.IsInducing.subtypeVal.comp e.isInducing
    exact (hi.isPreconnected_image.mp (himage.symm ▸ hconn)).image
      Subtype.val continuous_subtype_val.continuousOn
  obtain ⟨n, p, hn, hp0, hpn, hpi, hpU, hpe⟩ :=
    exists_edge_path_in_closed_vertex_partition K hK U' V' hU' hV' hcover' hinter'
      hconn' ha hb ((hmem U ⟨a, K.vertices_subset_space ha⟩).mpr haU)
      ((hmem U ⟨b, K.vertices_subset_space hb⟩).mpr hbU) hab
  refine ⟨n, p, hn, hp0, hpn, hpi,
    fun k hk ↦ hcover' ▸ Or.inl (hpU k hk), ?_⟩
  intro k hk
  exact ⟨(hpe k hk).1, fun x hx ↦ (hmem U x).mp ((hpe k hk).2 hx)⟩

end PoincareConjecture.M76.Dehn

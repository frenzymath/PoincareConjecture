import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSignPerturbation
import PoincareConjecture.Proofs.M76.Mathlib.HalfspaceGraphConnectivity
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedSignedPolygonZeros
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in


theorem mem_both_height_closures_of_strict_sign_preservation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 2)
    (A B : E →ᵃ[ℝ] ℝ)
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B v)
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B v < 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | A x < 0}) ∧
        v ∈ closure (K.space ∩ {x | 0 < A x}))
    (hedges : ∀ s ∈ K.faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0)
    {x : E} (hx : x ∈ K.space) (hxB : B x = 0) :
    x ∈ closure (K.space ∩ {y | B y < 0}) ∧
      x ∈ closure (K.space ∩ {y | 0 < B y}) := by
  have hzeroB (v : E) (hv : v ∈ K.vertices) (hvB : B v = 0) : A v = 0 := by
    rcases lt_trichotomy (A v) 0 with hn | hz | hp
    · exact False.elim ((hneg v hv hn).ne hvB)
    · exact hz
    · exact False.elim ((hpos v hv hp).ne' hvB)
  have hfaceSigns (s : Finset E) (hs : s ∈ K.faces)
      (hxs : x ∈ convexHull ℝ (s : Set E))
      (hnegn : ∃ v ∈ s, B v < 0) (hposn : ∃ v ∈ s, 0 < B v) :
      x ∈ closure (K.space ∩ {y | B y < 0}) ∧
        x ∈ closure (K.space ∩ {y | 0 < B y}) := by
    obtain ⟨v, hv, hvB⟩ := hnegn
    obtain ⟨w, hw, hwB⟩ := hposn
    have hn := (convex_convexHull ℝ (s : Set E)).mem_closure_lower_affine_height B
      hxs (subset_convexHull ℝ _ hv) (hxB.symm ▸ hvB)
    have hp := (convex_convexHull ℝ (s : Set E)).mem_closure_upper_affine_height B
      hxs (subset_convexHull ℝ _ hw) (hxB.symm ▸ hwB)
    rw [hxB] at hn hp
    exact ⟨closure_mono (inter_subset_inter_left _ (K.convexHull_subset_space hs)) hn,
      closure_mono (inter_subset_inter_left _ (K.convexHull_subset_space hs)) hp⟩
  by_cases hxv : x ∈ K.vertices
  · obtain ⟨hn, hp⟩ := hzero x hxv (hzeroB x hxv hxB)
    obtain ⟨v, hxv', hvA⟩ := K.exists_positive_graph_neighbor_of_mem_closure
      hK A ⟨x, hxv⟩ (hzeroB x hxv hxB) hp
    obtain ⟨w, hxw, hwA⟩ := K.exists_positive_graph_neighbor_of_mem_closure
      hK (-A) ⟨x, hxv⟩ (by simpa using congrArg Neg.neg (hzeroB x hxv hxB))
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hn)
    have hedge {v : K.vertices} (ha : K.vertexAbstractComplex.edgeGraph.Adj ⟨x, hxv⟩ v) :
        ({x, (v : E)} : Finset E) ∈ K.faces := by
      have h := ha.2
      change ({(⟨x, hxv⟩ : K.vertices), v} : Finset K.vertices).map
        (Function.Embedding.subtype _) ∈ K.faces at h
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
    have hn' := (convex_segment x (w : E)).mem_closure_lower_affine_height B
      (left_mem_segment ℝ x (w : E)) (right_mem_segment ℝ x (w : E))
      (hxB.symm ▸ hneg w w.property (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hwA))
    have hp' := (convex_segment x (v : E)).mem_closure_upper_affine_height B
      (left_mem_segment ℝ x (v : E)) (right_mem_segment ℝ x (v : E))
      (hxB.symm ▸ hpos v v.property hvA)
    rw [hxB] at hn' hp'
    have hseg (v : K.vertices) (ha : K.vertexAbstractComplex.edgeGraph.Adj ⟨x, hxv⟩ v) :
        segment ℝ x (v : E) ⊆ K.space := by
      simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space (hedge ha)
    exact ⟨closure_mono (inter_subset_inter_left _ (hseg w hxw)) hn',
      closure_mono (inter_subset_inter_left _ (hseg v hxv')) hp'⟩
  · obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hx
    have hs2 : s.card = 2 := by
      have hlo := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
      have hhi := hbound s hs
      have hne : s.card ≠ 1 := by
        intro h
        obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
        have hxv' : x = v := by
          simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
            intrinsicInterior_subset hxs
        exact hxv (hxv'.symm ▸ hs)
      omega
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hs2
    have hxu : x ≠ u := fun h => hxv (h.symm ▸ K.face_subset_vertices hs (by simp))
    have hxv' : x ≠ v := fun h => hxv (h.symm ▸ K.face_subset_vertices hs (by simp))
    have hxseg : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right
      hxu.symm hxv'.symm (by simpa only [Finset.coe_pair, convexHull_pair] using
        intrinsicInterior_subset hxs)
    obtain ⟨t, ht, htx⟩ := (openSegment_eq_image_lineMap ℝ u v).symm ▸ hxseg
    have hcomb : (1 - t) * B u + t * B v = 0 := by
      rw [← htx, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] at hxB
      exact hxB
    have hnonzero : B u ≠ 0 ∨ B v ≠ 0 := by
      by_contra! h
      obtain ⟨z, hz, hzA⟩ := hedges {u, v} hs (by simp [huv])
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz :
        z = u ∨ z = v) with hzu | hzv
      · exact hzA (hzu ▸ hzeroB u (K.face_subset_vertices hs (by simp)) h.1)
      · exact hzA (hzv ▸ hzeroB v (K.face_subset_vertices hs (by simp)) h.2)
    have hsign : (B u < 0 ∧ 0 < B v) ∨ (B v < 0 ∧ 0 < B u) := by
      have ht0 := ht.1
      have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
      rcases lt_trichotomy (B u) 0 with hu | hu | hu
      · left
        refine ⟨hu, ?_⟩
        have hleft := mul_neg_of_pos_of_neg ht1 hu
        nlinarith
      · exfalso
        have hv : B v = 0 := by
          rw [hu, mul_zero, zero_add] at hcomb
          exact (mul_eq_zero.mp hcomb).resolve_left ht0.ne'
        exact hnonzero.elim (fun h => h hu) (fun h => h hv)
      · right
        refine ⟨?_, hu⟩
        have hleft := mul_pos ht1 hu
        nlinarith
    apply hfaceSigns {u, v} hs (intrinsicInterior_subset hxs)
    · rcases hsign with h | h
      · exact ⟨u, by simp, h.1⟩
      · exact ⟨v, by simp, h.1⟩
    · rcases hsign with h | h
      · exact ⟨v, by simp, h.2⟩
      · exact ⟨u, by simp, h.2⟩




theorem ncard_polygon_zero_eq_two_of_strict_sign_preservation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 2)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPK : P.boundary ℝ = K.space)
    (A B : E →ᵃ[ℝ] ℝ)
    (hn : IsPreconnected (K.space ∩ {x | A x < 0}))
    (hp : IsPreconnected (K.space ∩ {x | 0 < A x}))
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B v)
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B v < 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | A x < 0}) ∧
        v ∈ closure (K.space ∩ {x | 0 < A x}))
    (hedges : ∀ s ∈ K.faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0)
    (hnegn : ∃ v ∈ K.vertices, A v < 0)
    (hposn : ∃ v ∈ K.vertices, 0 < A v) :
    (K.space ∩ {x | B x = 0}).ncard = 2 := by
  have hpg := K.preconnected_positive_vertex_graph_of_sign_preservation hK A B hp
    hpos hneg (fun v hv hz => (hzero v hv hz).2)
  have hng := K.preconnected_positive_vertex_graph_of_sign_preservation hK (-A) (-B)
    (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hn)
    (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg)
    (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] using hpos)
    (by intro v hv hz
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
          (hzero v hv (neg_eq_zero.mp hz)).1)
  have hnB := K.isPreconnected_positive_space_of_vertex_graph (-B) hng
  have hpB := K.isPreconnected_positive_space_of_vertex_graph B hpg
  rw [← hPK]
  apply P.ncard_zero_eq_two_of_preconnected_signs hP hinj B
    B.continuous_of_finiteDimensional.continuousOn
  · simpa only [hPK, AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hnB
  · simpa only [hPK] using hpB
  · intro x hx hxB
    simpa only [hPK] using K.mem_both_height_closures_of_strict_sign_preservation
      hK hbound A B hpos hneg hzero hedges (hPK.subset hx) hxB
  · obtain ⟨v, hv, hvA⟩ := hnegn
    exact ⟨v, hPK.symm.subset (K.vertices_subset_space hv), hneg v hv hvA⟩
  · obtain ⟨v, hv, hvA⟩ := hposn
    exact ⟨v, hPK.symm.subset (K.vertices_subset_space hv), hpos v hv hvA⟩

end Geometry.SimplicialComplex

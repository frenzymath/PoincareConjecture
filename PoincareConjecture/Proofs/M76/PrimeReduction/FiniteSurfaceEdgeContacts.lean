import PoincareConjecture.Proofs.M76.PrimeReduction.AffineContactFiniteness
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors











set_option autoImplicit false

open Set Module

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem vertex_avoidance_and_finite_edge_contacts
    (K T : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : finrank ℝ E = 3)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) {Z : Set E}
    (hZ : Disjoint Z T.vertices)
    (hZedge : ∀ t ∈ T.faces, t.card ≤ 2 → (Z ∩ convexHull ℝ (t : Set E)).Finite)
    (hposition : ∀ s ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ Z ∨
        ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E))) :
    Disjoint K.space T.vertices ∧
      ∀ t ∈ T.faces, t.card ≤ 2 →
        (K.space ∩ convexHull ℝ (t : Set E)).Finite := by
  classical
  have hrank (s : Finset E) (hs : s ∈ K.faces) :
      finrank ℝ (affineSpan ℝ (s : Set E)).direction ≤ 2 :=
    finrank_affineSpan_finset_le (K.nonempty_of_mem_faces hs) (hcard s hs)
  constructor
  · apply Set.disjoint_left.mpr
    intro x hxK hxT
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
    have hxt : x ∈ convexHull ℝ (({x} : Finset E) : Set E) := by simp
    rcases hposition s hs with hz | hpos
    · exact Set.disjoint_left.mp hZ (hz (intrinsicInterior_subset hxs)) hxT
    · rcases hpos {x} hxT with hspan | hdisjoint
      · have ht := finrank_affineSpan_finset_le (Finset.singleton_nonempty x)
          (d := 0) (by simp)
        have hd := AffineSubspace.disjoint_convexHulls_of_span_top_of_rank_lt hspan
          (by rw [hdim]; have := hrank s hs; omega)
        exact Set.disjoint_left.mp hd (intrinsicInterior_subset hxs) hxt
      · exact Set.disjoint_left.mp hdisjoint hxs hxt
  · intro t ht htc
    have htRank : finrank ℝ (affineSpan ℝ (t : Set E)).direction ≤ 1 :=
      finrank_affineSpan_finset_le (T.nonempty_of_mem_faces ht) htc
    let C : Finset E → Set E := fun s =>
      intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩ convexHull ℝ (t : Set E)
    have hC (s : Finset E) (hs : s ∈ K.faces) : (C s).Finite := by
      rcases hposition s hs with hz | hpos
      · exact (hZedge t ht htc).subset (fun _ hx =>
          ⟨hz (intrinsicInterior_subset hx.1), hx.2⟩)
      · rcases hpos t ht with hspan | hdisjoint
        · have hr : finrank ℝ (affineSpan ℝ (s : Set E)).direction +
              finrank ℝ (affineSpan ℝ (t : Set E)).direction ≤ finrank ℝ E := by
            rw [hdim]
            exact (Nat.add_le_add (hrank s hs) htRank)
          exact (subsingleton_convexHulls_inter_of_span_top_of_rank_le hspan hr).finite.subset
            (fun _ hx => ⟨intrinsicInterior_subset hx.1, hx.2⟩)
        · have he : C s = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisjoint
          rw [he]
          exact Set.finite_empty
    apply (hK.biUnion hC).subset
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hx.1
    exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, ⟨hxs, hx.2⟩⟩⟩

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteSurfaceEdgeContacts
import PoincareConjecture.Proofs.M76.PrimeReduction.AffinePlaneLineCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms

set_option autoImplicit false

open Set Module

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_transverse_surface_edge_chart
    (A T : SimplicialComplex ℝ E) (hA : A.faces.Finite) (hT : T.faces.Finite)
    (hdim : finrank ℝ E = 3) (hcard : ∀ s ∈ A.faces, s.card ≤ 3)
    (hvertices : Disjoint A.space T.vertices) {Z : Set E}
    (hposition : ∀ s ∈ A.faces,
      convexHull ℝ (s : Set E) ⊆ Z ∨
        ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E)))
    {t : Finset E} (ht : t ∈ T.faces) (htc : t.card = 2)
    {p : E} (hpA : p ∈ A.space) (hpt : p ∈ convexHull ℝ (t : Set E))
    (hpZ : p ∉ Z) :
    ∃ (U : Set E) (F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
      IsOpen U ∧ p ∈ U ∧ F 0 = p ∧
        (∀ z, F z ∈ U → (F z ∈ A.space ↔ z.2 = 0)) ∧
        ∀ z, F z ∈ U → (F z ∈ convexHull ℝ (t : Set E) ↔ z.1 = 0) := by
  classical
  obtain ⟨s, hs, hps⟩ := A.exists_face_intrinsicInterior_of_finite hA hpA
  have hspan : affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ := by
    rcases hposition s hs with hZ | hpos
    · exact (hpZ (hZ (intrinsicInterior_subset hps))).elim
    · rcases hpos t ht with hspan | hdisjoint
      · exact hspan
      · exact (Set.disjoint_left.mp hdisjoint hps hpt).elim
  let P := affineSpan ℝ (s : Set E)
  let Q := affineSpan ℝ (t : Set E)
  have hpP : p ∈ P :=
    convexHull_subset_affineSpan (s := (s : Set E)) (intrinsicInterior_subset hps)
  have hpQ : p ∈ Q := convexHull_subset_affineSpan (s := (t : Set E)) hpt
  have hPQ : P ⊔ Q = ⊤ := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have hPbound : finrank ℝ P.direction ≤ 2 :=
    finrank_affineSpan_finset_le (A.nonempty_of_mem_faces hs) (hcard s hs)
  have hQbound : finrank ℝ Q.direction ≤ 1 :=
    finrank_affineSpan_finset_le (T.nonempty_of_mem_faces ht) (by omega)
  have hrank := P.finrank_inf_add_ambient_of_mem_of_sup_top Q hpP hpQ hPQ
  have hP : finrank ℝ P.direction = 2 := by omega
  have hQ : finrank ℝ Q.direction = 1 := by omega
  have hsc : s.card = 3 := by
    have hscbound := hcard s hs
    by_contra hne
    have hlower : finrank ℝ P.direction ≤ 1 :=
      finrank_affineSpan_finset_le (A.nonempty_of_mem_faces hs) (by omega)
    omega
  have hmax : ∀ b ∈ A.faces, s ⊆ b → b = s := by
    intro b hb hsb
    exact (Finset.eq_of_subset_of_card_le hsb (by have := hcard b hb; omega)).symm
  have hptInterior : p ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) := by
    obtain ⟨u, hu, hpu⟩ := T.exists_face_intrinsicInterior_of_finite hT
      (T.convexHull_subset_space ht hpt)
    have hut := T.subset_of_mem_intrinsicInterior_face hu ht hpu hpt
    have hucbound := Finset.card_le_card hut
    have hucpos := Finset.card_pos.mpr (T.nonempty_of_mem_faces hu)
    have huc : u.card = 2 := by
      by_contra hne
      have hone : u.card = 1 := by omega
      obtain ⟨v, huv⟩ := Finset.card_eq_one.mp hone
      have hpv : p = v := by
        simpa only [huv, Finset.coe_singleton, convexHull_singleton,
          Set.mem_singleton_iff] using (intrinsicInterior_subset hpu)
      have hv : v ∈ T.vertices := by
        change {v} ∈ T.faces
        simpa only [huv] using hu
      exact Set.disjoint_left.mp hvertices (hpv ▸ hpA) hv
    have hutEq : u = t := Finset.eq_of_subset_of_card_le hut (by omega)
    simpa only [hutEq] using hpu
  obtain ⟨U, hU, hpU, hUA⟩ := A.exists_open_maximal_face_affine_germ hA hs hmax hps
  obtain ⟨V, hV, hpV, hVQ⟩ :=
    Set.exists_open_affine_germ_of_mem_intrinsicInterior hptInterior
  obtain ⟨F, hF, hFP, hFQ⟩ :=
    P.exists_centered_plane_line_coordinates Q hdim hP hQ hpP hpQ hPQ
  refine ⟨U ∩ V, F, hU.inter hV, ⟨hpU, hpV⟩, hF, ?_, ?_⟩
  · intro z hz
    exact (hUA (F z) hz.1).trans (hFP z)
  · intro z hz
    have hlocal : F z ∈ convexHull ℝ (t : Set E) ↔ F z ∈ Q := by
      simpa only [affineSpan_convexHull] using hVQ (F z) hz.2
    exact hlocal.trans (hFQ z)

end Geometry.SimplicialComplex

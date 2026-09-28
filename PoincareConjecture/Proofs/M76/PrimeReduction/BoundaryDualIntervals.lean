import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem barycentricDualBlock_space_of_single_coface
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t)
    (hcofaces : ∀ u ∈ K.faces, s ⊆ u → u = s ∨ u = t) :
    (K.barycentricDualBlock s).space =
      segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) := by
  classical
  let c : Finset E → E := fun u => u.centroid ℝ id
  have hedge : {c s, c t} ∈ (K.barycentricDualBlock s).faces := by
    refine ⟨?_, ?_⟩
    · apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
      refine ⟨{s, t}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hs
        · exact Finset.mem_singleton.mp hu ▸ ht
      · intro u hu v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact Or.inl Subset.rfl
        · exact Or.inl hst
        · exact Or.inr hst
        · exact Or.inl Subset.rfl
      · simp only [Finset.image_insert, Finset.image_singleton]
        rfl
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨s, hs, Subset.rfl, rfl⟩
      · exact ⟨t, ht, hst, (Finset.mem_singleton.mp hx).symm⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
    rw [← convexHull_pair]
    apply convexHull_mono (s := (a : Set E)) ?_ hxa
    intro z hz
    obtain ⟨u, hu, hsu, huz⟩ := ha.2 z hz
    rcases hcofaces u hu hsu with rfl | rfl
    · exact Or.inl huz.symm
    · exact Or.inr huz.symm
  · intro x hx
    apply (K.barycentricDualBlock s).convexHull_subset_space hedge
    simpa only [Finset.coe_pair, convexHull_pair] using hx

theorem barycentricDualBlock_space_of_maximal
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s) :
    (K.barycentricDualBlock s).space = {s.centroid ℝ id} := by
  simpa only [segment_same] using
    K.barycentricDualBlock_space_of_single_coface hs hs Subset.rfl
      (fun t ht hst => Or.inl (hmax t ht hst))

theorem barycentricDualBlock_boundary_interval
    (L : SimplicialComplex ℝ E) [Finite L.faces] (hLK : L ≤ K)
    {n : ℕ} (hKcard : ∀ u ∈ K.faces, u.card ≤ n + 1)
    (hLcard : ∀ u ∈ L.faces, u.card ≤ n)
    {s t : Finset E} (hs : s ∈ L.faces) (hscard : s.card = n)
    (ht : t ∈ K.faces) (htcard : t.card = n + 1) (hst : s ⊆ t)
    (hunique : ∀ u ∈ K.faces, u.card = n + 1 → s ⊆ u → u = t) :
    (K.barycentricDualBlock s).space =
        segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∧
      (K.barycentricDualBlock s).space ∩ L.space = {s.centroid ℝ id} ∧
      s.centroid ℝ id ≠ t.centroid ℝ id := by
  let : Fintype L.faces := Fintype.ofFinite _
  have hcofaces (u : Finset E) (hu : u ∈ K.faces) (hsu : s ⊆ u) :
      u = s ∨ u = t := by
    by_cases hus : u = s
    · exact Or.inl hus
    · have hlt := Finset.card_lt_card
        (hsu.ssubset_of_ne (fun h => hus h.symm))
      have hle := hKcard u hu
      exact Or.inr (hunique u hu (by omega) hsu)
  refine ⟨K.barycentricDualBlock_space_of_single_coface (hLK hs) ht hst hcofaces,
    ?_, ?_⟩
  · rw [K.barycentricDualBlock_space_inter_subcomplex L hLK]
    apply L.barycentricDualBlock_space_of_maximal hs
    intro u hu hsu
    exact (Finset.eq_of_subset_of_card_le hsu (by
      rw [hscard]
      exact hLcard u hu)).symm
  · intro h
    have he : (⟨s, hLK hs⟩ : K.faces) = ⟨t, ht⟩ := K.faceCentroid_injective h
    have hst' : s = t := congrArg Subtype.val he
    rw [hst'] at hscard
    omega

end Geometry.SimplicialComplex

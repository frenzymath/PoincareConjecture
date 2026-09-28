import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]




theorem barycentricDualBlock_of_single_coface
    {n : ℕ} (hcard : ∀ v ∈ K.faces, v.card ≤ n + 1)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hscard : s.card = n) (htcard : t.card = n + 1) (hst : s ⊆ t)
    (hcofaces : ∀ v ∈ K.faces, s ⊆ v → v.card = n + 1 → v = t) :
    (K.barycentricDualBlock s).space = segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∧
      IsFinitePLBallPair ℝ (K.barycentricDualBlock s).space
        {s.centroid ℝ id, t.centroid ℝ id} ∧
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id} := by
  classical
  let c : Finset E → E := fun v => v.centroid ℝ id
  have hcinj {v w : Finset E} (hv : v ∈ K.faces) (hw : w ∈ K.faces)
      (he : c v = c w) : v = w := by
    have h : (⟨v, hv⟩ : K.faces) = ⟨w, hw⟩ := K.faceCentroid_injective he
    exact congrArg Subtype.val h
  have hne : c s ≠ c t := by
    intro he
    have hst' := hcinj hs ht he
    rw [hst'] at hscard
    omega
  have hedge : ({c s, c t} : Finset E) ∈ (K.barycentricDualBlock s).faces := by
    refine ⟨?_, ?_⟩
    · apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
      refine ⟨{s, t}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hs
        · exact Finset.mem_singleton.mp hv ▸ ht
      · intro v hv w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
        rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
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
  have hcarrier : (K.barycentricDualBlock s).space = segment ℝ (c s) (c t) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
      rw [← convexHull_pair]
      apply convexHull_mono (s := (a : Set E)) ?_ hxa
      intro y hy
      obtain ⟨v, hv, hsv, hvy⟩ := ha.2 y hy
      by_cases hvs : v = s
      · exact Or.inl (hvy.symm.trans (congrArg c hvs))
      · have hlt := Finset.card_lt_card
          (hsv.ssubset_of_ne (fun he => hvs he.symm))
        have hle := hcard v hv
        have hvt := hcofaces v hv hsv (by omega)
        exact Or.inr (hvy.symm.trans (congrArg c hvt))
    · intro x hx
      apply (K.barycentricDualBlock s).convexHull_subset_space hedge
      simpa only [Finset.coe_pair, convexHull_pair] using hx
  have hball := isFinitePLBallPair_affine_interval
    (show (0 : ℝ) < 1 from zero_lt_one) (ContinuousAffineMap.lineMap (c s) (c t))
    (AffineMap.lineMap_injective ℝ hne).injOn
  have hball' : IsFinitePLBallPair ℝ (segment ℝ (c s) (c t)) {c s, c t} := by
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using hball
  refine ⟨hcarrier, hcarrier.symm ▸ hball', ?_⟩
  simpa using K.barycentricDualBlock_link_space_of_paired_facet
    hcard hs ht ht hscard htcard htcard hst hst
    (fun v hv hsv hvc => Or.inl (hcofaces v hv hsv hvc))

end Geometry.SimplicialComplex

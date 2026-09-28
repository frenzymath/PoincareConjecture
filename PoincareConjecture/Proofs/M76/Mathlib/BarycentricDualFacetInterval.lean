import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualBlocks
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [FiniteDimensional ℝ E] in


private theorem centroid_pair_face [DecidableEq E]
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t) :
    {s.centroid ℝ id, t.centroid ℝ id} ∈ K.barycentricSubdivision.faces := by
  apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
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





theorem isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    {n : ℕ} (hcard : ∀ t ∈ K.faces, t.card ≤ n + 1)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hscard : s.card = n) (htcard : t.card = n + 1) (hucard : u.card = n + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (hcofaces : ∀ v ∈ K.faces, s ⊆ v → v.card = n + 1 → v = t ∨ v = u) :
    IsFinitePLBallPair ℝ (K.barycentricDualBlock s).space
      {t.centroid ℝ id, u.centroid ℝ id} ∧
      s.centroid ℝ id ∈ (K.barycentricDualBlock s).space \
        {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  let c : Finset E → E := fun v => v.centroid ℝ id
  have hstne : s ≠ t := by intro h; rw [h] at hscard; omega
  have hsune : s ≠ u := by intro h; rw [h] at hscard; omega
  have hcinj {a b : Finset E} (ha : a ∈ K.faces) (hb : b ∈ K.faces)
      (hab : c a = c b) : a = b := by
    have h : (⟨a, ha⟩ : K.faces) = ⟨b, hb⟩ := K.faceCentroid_injective hab
    exact congrArg Subtype.val h
  have hcst : c s ≠ c t := fun h => hstne (hcinj hs ht h)
  have hcsu : c s ≠ c u := fun h => hsune (hcinj hs hu h)
  have hctu : c t ≠ c u := fun h => htu (hcinj ht hu h)
  have hedge (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v) :
      ({c s, c v} : Finset E) ∈ (K.barycentricDualBlock s).faces := by
    refine ⟨K.centroid_pair_face hs hv hsv, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨s, hs, Subset.rfl, rfl⟩
    · exact ⟨v, hv, hsv, Finset.mem_singleton.mp hz |>.symm⟩
  have hcarrier : (K.barycentricDualBlock s).space =
      segment ℝ (c t) (c s) ∪ segment ℝ (c s) (c u) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
      obtain ⟨b, hb, hfaces, hchain, heq⟩ :=
        (K.barycentricSubdivision_faces_of_face_chains a).mp ha.1
      have hsface (v : Finset E) (hv : v ∈ b) : s ⊆ v := by
        have hcv : c v ∈ a := heq.symm ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hsw, hwv⟩ := ha.2 _ hcv
        exact hcinj hw (hfaces v hv) hwv ▸ hsw
      obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal hb
      have hvm (v : Finset E) (hv : v ∈ b) : v ⊆ m := by
        rcases hchain v hv m hm with h | h
        · exact h
        · exact hmax hv h
      have hclass (v : Finset E) (hv : v ∈ b) : v = s ∨ v = t ∨ v = u := by
        by_cases hvs : v = s
        · exact Or.inl hvs
        · have hlt := Finset.card_lt_card
            ((hsface v hv).ssubset_of_ne (fun h => hvs h.symm))
          have hle := hcard v (hfaces v hv)
          exact Or.inr (hcofaces v (hfaces v hv) (hsface v hv) (by omega))
      have hsub (v : Finset E) (hv : v ∈ b) : v = s ∨ v = m := by
        rcases hclass v hv with hvs | hvt | hvu
        · exact Or.inl hvs
        · exact Or.inr (Finset.eq_of_subset_of_card_le (hvm v hv)
            (by have h := hcard m (hfaces m hm); rw [hvt, htcard]; exact h))
        · exact Or.inr (Finset.eq_of_subset_of_card_le (hvm v hv)
            (by have h := hcard m (hfaces m hm); rw [hvu, hucard]; exact h))
      have hxseg : x ∈ segment ℝ (c s) (c m) := by
        rw [← convexHull_pair]
        apply convexHull_mono (s := (a : Set E)) ?_ hxa
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (heq ▸ hz)
        rcases hsub v hv with h | h
        · exact Or.inl (congrArg c h)
        · exact Or.inr (congrArg c h)
      rcases hclass m hm with hms | hmt | hmu
      · have hxs : x = c s := by simpa only [hms, segment_same, mem_singleton_iff] using hxseg
        exact Or.inl (hxs.symm ▸ right_mem_segment ℝ (c t) (c s))
      · exact Or.inl (by simpa only [hmt, segment_symm] using hxseg)
      · exact Or.inr (by simpa only [hmu] using hxseg)
    · rintro (hx | hx)
      · apply (K.barycentricDualBlock s).convexHull_subset_space (hedge t ht hst)
        simpa only [Finset.coe_pair, convexHull_pair, segment_symm] using hx
      · apply (K.barycentricDualBlock s).convexHull_subset_space (hedge u hu hsu)
        simpa only [Finset.coe_pair, convexHull_pair] using hx
  have hinter : segment ℝ (c t) (c s) ∩ segment ℝ (c s) (c u) = {c s} := by
    apply Subset.antisymm
    · intro x hx
      have hcommon := K.barycentricSubdivision.inter_subset_convexHull
        (hedge t ht hst).1 (hedge u hu hsu).1
        ⟨by simpa only [Finset.coe_pair, convexHull_pair, segment_symm] using hx.1,
          by simpa only [Finset.coe_pair, convexHull_pair] using hx.2⟩
      have hpair : ({c s, c t} : Set E) ∩ {c s, c u} = {c s} := by
        ext y
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨h | h, k | k⟩
          · exact h
          · exact h
          · exact k
          · exact (hctu (h.symm.trans k)).elim
        · intro h
          exact ⟨Or.inl h, Or.inl h⟩
      simpa only [Finset.coe_pair, hpair, convexHull_singleton] using hcommon
    · rintro x rfl
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  rw [hcarrier]
  exact ⟨Set.isFinitePLBallPair_two_segments hcst.symm hcsu hinter,
    Or.inl (right_mem_segment ℝ _ _), fun h => h.elim hcst hcsu⟩

end Geometry.SimplicialComplex

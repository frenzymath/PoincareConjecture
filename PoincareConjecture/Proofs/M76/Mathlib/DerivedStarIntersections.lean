import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarFaces

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem exists_common_face_of_mem_subcomplexes
    (K S T : SimplicialComplex ℝ E) (hS : S ≤ K) (hT : T ≤ K)
    {x : E} (hx : x ∈ S.space ∩ T.space) :
    ∃ s, s ∈ S.faces ∧ s ∈ T.faces ∧ x ∈ convexHull ℝ (s : Set E) := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx.2
  have hxi : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using
      K.inter_subset_convexHull (hS hs) (hT ht) ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxi⟩)
  exact ⟨s ∩ t, S.down_closed hs Finset.inter_subset_left hne,
    T.down_closed ht Finset.inter_subset_right hne, hxi⟩

variable (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

theorem mem_inter_derived_closedStars_iff
    {p q x : E} (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) :
    x ∈ ((K.derivedSubdivision c hc).closedStar p).space ∩
      ((K.derivedSubdivision c hc).closedStar q).space ↔
    ∃ a : Finset K.faces, a.Nonempty ∧
      (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
      (∀ s ∈ a, p ∈ s.val ∧ q ∈ s.val) ∧
      x ∈ convexHull ℝ (a.image c : Set E) := by
  constructor
  · intro hx
    obtain ⟨t, htp, htq, hxt⟩ :=
      (K.derivedSubdivision c hc).exists_common_face_of_mem_subcomplexes
        ((K.derivedSubdivision c hc).closedStar p)
        ((K.derivedSubdivision c hc).closedStar q)
        (fun _ h => h.1) (fun _ h => h.1) hx
    obtain ⟨a, ha, hchain, hta, hap⟩ :=
      (K.derivedSubdivision_closedStar_faces c hc hp t).mp htp
    obtain ⟨b, _, _, htb, hbq⟩ :=
      (K.derivedSubdivision_closedStar_faces c hc hq t).mp htq
    have hab : a = b := Finset.image_injective (K.positiveFaceCenter_injective c hc)
      (hta.symm.trans htb)
    refine ⟨a, ha, hchain, fun s hs => ⟨hap s hs, hbq s (hab ▸ hs)⟩, ?_⟩
    rwa [← hta]
  · rintro ⟨a, ha, hchain, hall, hx⟩
    exact ⟨convexHull_subset_space
      ((K.derivedSubdivision_closedStar_faces c hc hp _).mpr
        ⟨a, ha, hchain, rfl, fun s hs => (hall s hs).1⟩) hx,
      convexHull_subset_space
      ((K.derivedSubdivision_closedStar_faces c hc hq _).mpr
        ⟨a, ha, hchain, rfl, fun s hs => (hall s hs).2⟩) hx⟩

theorem pair_mem_faces_of_derivedStars_inter_nonempty
    {p q : E} (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces)
    (hne : (((K.derivedSubdivision c hc).closedStar p).space ∩
      ((K.derivedSubdivision c hc).closedStar q).space).Nonempty) :
    {p, q} ∈ K.faces := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, ha, _, hall, _⟩ := (K.mem_inter_derived_closedStars_iff c hc hp hq).mp hx
  obtain ⟨s, hs⟩ := ha
  exact K.down_closed s.property
    (Finset.insert_subset_iff.mpr
      ⟨(hall s hs).1, Finset.singleton_subset_iff.mpr (hall s hs).2⟩)
    (Finset.insert_nonempty p {q})

theorem derived_closedStars_inter_eq_dual_edge
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {p q : E} (hpq : p ≠ q) (he : {p, q} ∈ K.faces) :
    ((K.derivedSubdivision c hc).closedStar p).space ∩
      ((K.derivedSubdivision c hc).closedStar q).space =
      {x | ∃ t : K.faces, t.val.card = 3 ∧ {p, q} ⊆ t.val ∧
        x ∈ segment ℝ (c ⟨{p, q}, he⟩) (c t)} := by
  classical
  let e : K.faces := ⟨{p, q}, he⟩
  have hp : {p} ∈ K.faces := K.down_closed he (by simp) (Finset.singleton_nonempty p)
  have hq : {q} ∈ K.faces := K.down_closed he (by simp) (Finset.singleton_nonempty q)
  have hec : e.val.card = 2 := by simp [e, hpq]
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hchain, hall, hxa⟩ :=
      (K.mem_inter_derived_closedStars_iff c hc hp hq).mp hx
    obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
    have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
      rcases hchain i hi m hm with h | h
      · exact h
      · exact hmax hi h
    obtain ⟨t, ht, htc, hmt⟩ := hpure m.val m.property
    let t₀ : K.faces := ⟨t, ht⟩
    have hei (i : K.faces) (hi : i ∈ a) : e.val ⊆ i.val := by
      exact Finset.insert_subset_iff.mpr
        ⟨(hall i hi).1, Finset.singleton_subset_iff.mpr (hall i hi).2⟩
    refine ⟨t₀, htc, (hei m hm).trans hmt, ?_⟩
    have hsub : (a.image c : Set E) ⊆ {c e, c t₀} := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      by_cases hie : i = e
      · exact Or.inl (congrArg c hie)
      · have hei' : e.val ⊂ i.val :=
          (hei i hi).ssubset_of_ne (fun h => hie (Subtype.ext h.symm))
        have hi3 : i.val.card = 3 := by
          have hlo := Finset.card_lt_card hei'
          have hhi := Finset.card_le_card ((him i hi).trans hmt)
          omega
        have hit : i = t₀ := Subtype.ext (Finset.eq_of_subset_of_card_le
          ((him i hi).trans hmt) (by change t.card ≤ i.val.card; omega))
        exact Or.inr (congrArg c hit)
    rw [← convexHull_pair]
    exact convexHull_mono hsub hxa
  · rintro ⟨t, htc, het, hxt⟩
    apply (K.mem_inter_derived_closedStars_iff c hc hp hq).mpr
    refine ⟨{e, t}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
    · intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact Or.inl le_rfl
      · exact Or.inl het
      · exact Or.inr het
      · exact Or.inl le_rfl
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp [e]
      · exact ⟨het (Finset.mem_insert_self _ _),
          het (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
    · simpa only [Finset.image_insert, Finset.image_singleton,
        Finset.coe_pair, convexHull_pair] using hxt

end Geometry.SimplicialComplex

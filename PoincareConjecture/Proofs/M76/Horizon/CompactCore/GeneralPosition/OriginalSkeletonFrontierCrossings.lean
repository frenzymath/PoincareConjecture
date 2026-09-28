import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ChartLineCrossings
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation










set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph



theorem source_edge_frontier_alternative
    {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : OpenPartialHomeomorph X V) (g : E → X) (a b : E) {F : Set X}
    (hsource : ∀ r : I, g (AffineMap.lineMap a b (r : ℝ)) ∈ B.source)
    (hline : ∀ r : I, B (g (AffineMap.lineMap a b (r : ℝ))) =
      AffineMap.lineMap (B (g a)) (B (g b)) (r : ℝ))
    (ha : g a ∉ F) (hb : g b ∉ F)
    (hkind : Disjoint B.source F ∨ ∃ ell : V →ᴬ[ℝ] ℝ,
      ∀ y ∈ B.source, y ∈ F ↔ ell (B y) = 0) :
    segment ℝ a b ∩ g ⁻¹' F = ∅ ∨ ∃ r : I,
      0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧
      segment ℝ a b ∩ g ⁻¹' F = {AffineMap.lineMap a b (r : ℝ)} ∧
      AffineMap.lineMap a b (r : ℝ) ∈ openSegment ℝ a b := by
  let f : I → X := fun r => g (AffineMap.lineMap a b (r : ℝ))
  have hpreimage : segment ℝ a b ∩ g ⁻¹' F =
      (fun r : I => AffineMap.lineMap a b (r : ℝ)) '' (f ⁻¹' F) := by
    ext x
    constructor
    · rintro ⟨hx, hf⟩
      rw [segment_eq_image_lineMap] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨⟨r, hr⟩, hf, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨lineMap_mem_segment ℝ a b r.property, hr⟩
  have hfl (r : I) : B (f r) = AffineMap.lineMap (B (f 0)) (B (f 1)) (r : ℝ) := by
    simpa [f] using hline r
  rcases B.chart_line_frontier_alternative f hsource hfl
      (by simpa [f] using ha) (by simpa [f] using hb) hkind with hnone |
      ⟨r, _, hr0, hr1, hsingle, _⟩
  · exact Or.inl (by rw [hpreimage, hnone, image_empty])
  · refine Or.inr ⟨r, hr0, hr1, ?_, lineMap_mem_openSegment ℝ a b ⟨hr0, hr1⟩⟩
    rw [hpreimage, hsingle, image_singleton]

end OpenPartialHomeomorph

namespace Geometry.SimplicialComplex




theorem original_skeleton_frontier_crossings
    {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (a b : {s : K.faces // s.val.card = 2} → K.vertices)
    (hpair : ∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val)
    (T : SimplicialComplex ℝ E)
    (hTS : T.space = ⋃ k, segment ℝ (a k : E) (b k : E))
    (G : C(I × T.space, X)) (g : E → X) (p : K.vertices → C(I, X))
    {F : Set X} (hpoff : ∀ v, p v 1 ∉ F)
    (hG1 : ∀ x : T.space, G (1, x) = g x)
    (hend : ∀ k (t : I) (ha : (a k : E) ∈ T.space) (hb : (b k : E) ∈ T.space),
      G (t, ⟨a k, ha⟩) = p (a k) t ∧ G (t, ⟨b k, hb⟩) = p (b k) t)
    (B : K.vertices → OpenPartialHomeomorph X V)
    (hformula : ∀ k (t r : I)
      (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T.space),
      G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (B (a k)).source ∧
      B (a k) (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) =
        AffineMap.lineMap (B (a k) (p (a k) t)) (B (a k) (p (b k) t)) (r : ℝ))
    (hkind : ∀ v, Disjoint (B v).source F ∨ ∃ ell : V →ᴬ[ℝ] ℝ,
      ∀ y ∈ (B v).source, y ∈ F ↔ ell (B v y) = 0) :
    (∀ v : K.vertices, g v ∉ F) ∧
      (∀ k, (segment ℝ (a k : E) (b k : E) ∩ g ⁻¹' F).Subsingleton) ∧
      ∀ k, segment ℝ (a k : E) (b k : E) ∩ g ⁻¹' F = ∅ ∨ ∃ r : I,
        0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧
        segment ℝ (a k : E) (b k : E) ∩ g ⁻¹' F =
          {AffineMap.lineMap (a k : E) (b k : E) (r : ℝ)} ∧
        AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈
          openSegment ℝ (a k : E) (b k : E) := by
  classical
  have hedgeT (k : {s : K.faces // s.val.card = 2}) :
      segment ℝ (a k : E) (b k : E) ⊆ T.space :=
    fun _ hx => hTS.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)
  have hend' (k : {s : K.faces // s.val.card = 2}) :
      g (a k) = p (a k) 1 ∧ g (b k) = p (b k) 1 := by
    have ha := hedgeT k (left_mem_segment ℝ (a k : E) (b k : E))
    have hb := hedgeT k (right_mem_segment ℝ (a k : E) (b k : E))
    exact ⟨(hG1 ⟨a k, ha⟩).symm.trans (hend k 1 ha hb).1,
      (hG1 ⟨b k, hb⟩).symm.trans (hend k 1 ha hb).2⟩
  have hvertex (v : K.vertices) : g v ∉ F := by
    obtain ⟨s, hs, hvs, hc⟩ := K.exists_full_coface_of_convex_space hK hcv hne v.property
    have hv : (v : E) ∈ s := hvs (Finset.mem_singleton_self _)
    have hc3 : s.card = 3 := by omega
    have herase : (s.erase (v : E)).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hv, hc3]
      decide
    obtain ⟨w, hw⟩ := herase
    have he : {(v : E), w} ∈ K.faces := K.down_closed hs
      (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro hv (Finset.mem_erase.mp hw).2) (by simp)
    let k : {s : K.faces // s.val.card = 2} :=
      ⟨⟨{(v : E), w}, he⟩, Finset.card_pair (Finset.mem_erase.mp hw).1.symm⟩
    have hvpair : (v : E) = a k ∨ (v : E) = b k := by
      have hm : (v : E) ∈ ({(a k : E), (b k : E)} : Finset E) :=
        (hpair k).symm ▸ (show (v : E) ∈ k.val.val from Finset.mem_insert_self _ _)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hvpair with hvpair | hvpair
    · rw [hvpair, (hend' k).1]
      exact hpoff (a k)
    · rw [hvpair, (hend' k).2]
      exact hpoff (b k)
  have halt (k : {s : K.faces // s.val.card = 2}) :=
    (B (a k)).source_edge_frontier_alternative g (a k : E) (b k : E)
      (fun r => by
        have h := (hformula k 1 r (hedgeT k (lineMap_mem_segment ℝ _ _ r.property))).1
        rw [hG1] at h
        exact h)
      (fun r => by
        have h := (hformula k 1 r (hedgeT k (lineMap_mem_segment ℝ _ _ r.property))).2
        rw [hG1] at h
        simpa only [← (hend' k).1, ← (hend' k).2] using h)
      (hvertex (a k)) (hvertex (b k)) (hkind (a k))
  refine ⟨hvertex, ?_, halt⟩
  intro k
  rcases halt k with he | ⟨r, _, _, he, _⟩
  · rw [he]
    exact subsingleton_empty
  · rw [he]
    exact subsingleton_singleton

end Geometry.SimplicialComplex

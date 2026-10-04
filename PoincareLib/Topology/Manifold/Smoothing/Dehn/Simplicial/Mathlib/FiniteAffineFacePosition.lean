import PoincareLib.Topology.Manifold.Smoothing.Dehn.Affine.Mathlib.IntrinsicHullAffineExclusion
import Mathlib.Data.List.Nodup

/-!
# The last selected vertex gives the literal face alternative

Every other source image is either an earlier selected image or
an unchanged original vertex. The finite avoidance certificate
therefore applies to their union with the actual target face.
See Hudson1969, Lemma4.5, and Dehn029, section4.
-/

set_option autoImplicit false

open Set

namespace List

/-- Split a finite list at its last member belonging to a given
set, retaining the complete prefix and suffix. See Dehn029,
section4, for the last moved vertex of an actual face. -/
theorem exists_split_last_mem_set {α : Type*} (l : List α) (s : Set α)
    (h : ∃ v ∈ l, v ∈ s) :
    ∃ (p : List α) (v : α) (q : List α),
      l = p ++ v :: q ∧ v ∈ s ∧ ∀ w ∈ q, w ∉ s := by
  classical
  induction l with
  | nil =>
    obtain ⟨v, hv, _⟩ := h
    exact (List.not_mem_nil hv).elim
  | cons a l ih =>
    by_cases ht : ∃ v ∈ l, v ∈ s
    · obtain ⟨p, v, q, he, hv, hq⟩ := ih ht
      exact ⟨a :: p, v, q, by simp only [cons_append, he], hv, hq⟩
    · have ha : a ∈ s := by
        obtain ⟨v, hv, hs⟩ := h
        rcases mem_cons.mp hv with rfl | hv
        · exact hs
        · exact (ht ⟨v, hv, hs⟩).elim
      exact ⟨[], a, l, rfl, ha, fun w hw hs => ht ⟨w, hw, hs⟩⟩

end List

namespace Geometry

/-- The concrete prefix avoidance certificate gives full affine
span or disjoint source relative interior for each actual pair
of finite faces. Target points stay fixed comparison points.
See Dehn029, section4. -/
theorem affine_span_eq_top_or_disjoint_of_ordered_vertex_avoidance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List E) (f : E → E) (T : Set E)
    (havoid : ∀ (p : List E) (v : E) (q : List E), l = p ++ v :: q →
      ∀ S : Finset E, (S : Set E) ⊆ T ∪ f '' {w | w ∈ p} →
        affineSpan ℝ (S : Set E) ≠ ⊤ → f v ∉ affineSpan ℝ (S : Set E))
    (s t : Finset E) (hfree : ∃ v ∈ l, v ∈ s)
    (hfixed : ∀ w ∈ s, w ∉ l → f w ∈ T) (ht : (t : Set E) ⊆ T) :
    affineSpan ℝ (f '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (f '' (s : Set E))))
        (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨p, v, q, he, hv, hq⟩ := l.exists_split_last_mem_set (s : Set E) hfree
  let S : Finset E := (s.erase v).image f ∪ t
  have hSfull : (S : Set E) ⊆ f '' (s : Set E) ∪ (t : Set E) := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      exact Or.inl (mem_image_of_mem f (Finset.mem_erase.mp hw).2)
    · exact Or.inr hy
  by_cases htop : affineSpan ℝ (S : Set E) = ⊤
  · left
    apply top_unique
    rw [← htop]
    exact affineSpan_mono ℝ hSfull
  · right
    have hST : (S : Set E) ⊆ T ∪ f '' {w | w ∈ p} := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        have hwv := Finset.mem_erase.mp hw
        by_cases hwl : w ∈ l
        · have hwp : w ∈ p := by
            rw [he] at hwl
            rcases List.mem_append.mp hwl with hp | hq'
            · exact hp
            · rcases List.mem_cons.mp hq' with hewv | hwq
              · exact (hwv.1 hewv).elim
              · exact (hq w hwq hwv.2).elim
          exact Or.inr ⟨w, hwp, rfl⟩
        · exact Or.inl (hfixed w hwv.2 hwl)
      · exact Or.inl (ht hy)
    have hexcluded := havoid p v q he S hST htop
    apply AffineSubspace.disjoint_intrinsicInterior_convexHulls_of_excluded_vertex
      (mem_image_of_mem f hv)
    intro hmem
    apply hexcluded
    apply affineSpan_mono ℝ ?_ hmem
    rintro y (⟨⟨w, hw, rfl⟩, hne⟩ | hy)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨w, Finset.mem_erase.mpr ⟨?_, hw⟩, rfl⟩
      intro hewv
      exact hne (congrArg f hewv)
    · exact Finset.mem_union.mpr (Or.inr hy)

end Geometry

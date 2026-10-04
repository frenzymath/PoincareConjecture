import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedStarIntersections

/-!
# Shared derived stars lie in their links

The closed stars of nonadjacent vertices intersect inside both
links. Distinct original vertices are nonadjacent after derived
subdivision, since their singleton faces are incomparable.
See Hudson 1969, pp. 8--9 and M76 derivation 271.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

/-- Nonadjacent closed stars meet only in their links. The
common face omits both vertices, since either insertion
would otherwise contain their edge. See Hudson pp. 8--9
and M76 derivation 271. -/
theorem closedStars_inter_subset_links (K : SimplicialComplex ℝ E)
    {p q : E} (hno : {p, q} ∉ K.faces) :
    (K.closedStar p).space ∩ (K.closedStar q).space ⊆
      (K.link p).space ∩ (K.link q).space := by
  intro x hx
  obtain ⟨t, htp, htq, hxt⟩ :=
    K.exists_common_face_of_mem_subcomplexes (K.closedStar p) (K.closedStar q)
      (fun _ h => h.1) (fun _ h => h.1) hx
  have hp : p ∉ t := by
    intro hp
    apply hno
    apply K.down_closed htq.2 _ (Finset.insert_nonempty p {q})
    exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_insert_of_mem hp,
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self q t)⟩
  have hq : q ∉ t := by
    intro hq
    apply hno
    apply K.down_closed htp.2 _ (Finset.insert_nonempty p {q})
    exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_insert_self p t,
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem hq)⟩
  exact ⟨(K.link p).convexHull_subset_space ⟨htp.1, hp, htp.2⟩ hxt,
    (K.link q).convexHull_subset_space ⟨htq.1, hq, htq.2⟩ hxt⟩

variable (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

/-- Distinct original vertices never span a derived edge:
their singleton coarse faces cannot belong to one chain.
See Hudson pp. 8--9 and M76 derivation 271. -/
theorem pair_not_mem_derivedSubdivision_faces {p q : E}
    (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) (hpq : p ≠ q) :
    {p, q} ∉ (K.derivedSubdivision c hc).faces := by
  classical
  intro he
  obtain ⟨a, _, hchain, ha⟩ := (K.derivedSubdivision_faces c hc _).mp he
  let p₀ : K.faces := ⟨{p}, hp⟩
  let q₀ : K.faces := ⟨{q}, hq⟩
  have hcp : c p₀ = p := K.positiveFaceCenter_singleton c hc hp
  have hcq : c q₀ = q := K.positiveFaceCenter_singleton c hc hq
  have hinj := K.positiveFaceCenter_injective c hc
  have hp₀ : p₀ ∈ a := by
    have hmem : c p₀ ∈ a.image c := by rw [hcp, ← ha]; simp
    obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hmem
    exact hinj hip ▸ hi
  have hq₀ : q₀ ∈ a := by
    have hmem : c q₀ ∈ a.image c := by rw [hcq, ← ha]; simp
    obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hmem
    exact hinj hiq ▸ hi
  rcases hchain p₀ hp₀ q₀ hq₀ with h | h
  · exact hpq (Finset.mem_singleton.mp (h (Finset.mem_singleton_self p)))
  · exact hpq (Finset.mem_singleton.mp (h (Finset.mem_singleton_self q))).symm

/-- The full overlap of distinct original-vertex derived
stars belongs to both actual links. See Hudson pp. 8--9
and M76 derivation 271. -/
theorem derived_closedStars_inter_subset_links {p q : E}
    (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) (hpq : p ≠ q) :
    ((K.derivedSubdivision c hc).closedStar p).space ∩
        ((K.derivedSubdivision c hc).closedStar q).space ⊆
      ((K.derivedSubdivision c hc).link p).space ∩
        ((K.derivedSubdivision c hc).link q).space :=
  (K.derivedSubdivision c hc).closedStars_inter_subset_links
    (K.pair_not_mem_derivedSubdivision_faces c hc hp hq hpq)

end Geometry.SimplicialComplex

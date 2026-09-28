import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralCoverageCriterion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension

set_option autoImplicit false

open Set
open scoped Topology

namespace Geometry.SimplicialComplex

section Incidence

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

def HasTwoFullCofaces (K : SimplicialComplex 𝕜 E) (n : ℕ) (s : Finset E) : Prop :=
  ∃ t ∈ K.faces, ∃ u ∈ K.faces,
    s ⊆ t ∧ s ⊆ u ∧ t.card = n + 1 ∧ u.card = n + 1 ∧ t ≠ u

end Incidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem covers_convex_open_of_paired_facets (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces,
      s ⊆ t ∧ t.card = Module.finrank ℝ E + 1)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hmeet : (U ∩ K.space).Nonempty)
    (hpair : ∀ s ∈ K.faces, s.card = Module.finrank ℝ E →
      (convexHull ℝ (s : Set E) ∩ U).Nonempty →
        K.HasTwoFullCofaces (Module.finrank ℝ E) s) : U ⊆ K.space := by
  classical
  let S : Set (Finset E) := {s | s ∈ K.faces ∧ s.card < Module.finrank ℝ E}
  have hS : S.Finite := hfinite.subset (fun _ hs => hs.1)
  let : Finite S := hS.to_subtype
  let A : S → AffineSubspace ℝ E := fun s => affineSpan ℝ (s.val : Set E)
  have hA : ∀ s, Module.finrank ℝ (A s).direction + 1 < Module.finrank ℝ E := by
    intro s
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces s.property.1)
    have hc : s.val.card = (s.val.card - 1) + 1 := by omega
    change Module.finrank ℝ (affineSpan ℝ (s.val : Set E)).direction + 1 < _
    rw [K.finrank_faceDirection_of_card s.property.1 hc]
    have hslt := s.property.2
    omega
  have hmeetint : (U ∩ interior K.space).Nonempty := by
    obtain ⟨x, hxU, hxK⟩ := hmeet
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxK
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    let b := (K.indep ht).affineBasisOfCard htcard
    have hnonempty : (interior (convexHull ℝ (t : Set E))).Nonempty := by
      apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
      simpa [b] using b.tot
    have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst hxs
    have hxcl : x ∈ closure (interior (convexHull ℝ (t : Set E))) := by
      rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hnonempty]
      exact subset_closure hxt
    obtain ⟨y, hyU, hyint⟩ := mem_closure_iff.mp hxcl U hU hxU
    exact ⟨y, hyU, interior_mono (K.convexHull_subset_space ht) hyint⟩
  apply (K.isCompact_space_of_finite hfinite).isClosed.covers_of_interior_off_affineSubspaces
    hU hconv hmeetint A hA
  intro x hxU hxK hxA
  obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hfinite hxK
  have hscard : Module.finrank ℝ E ≤ s.card := by
    by_contra h
    have hsmall : s ∈ S := ⟨hs, not_le.mp h⟩
    apply hxA
    exact mem_iUnion.mpr ⟨⟨s, hsmall⟩,
      convexHull_subset_affineSpan _ (intrinsicInterior_subset hxs)⟩
  obtain ⟨v, hv, hsv, hvcard⟩ := hpure s hs
  have hsle := Finset.card_le_card hsv
  by_cases hsfull : s.card = Module.finrank ℝ E + 1
  · exact K.mem_interior_space_of_full_face hs hsfull hxs
  · have hsfacet : s.card = Module.finrank ℝ E := by omega
    obtain ⟨t, ht, u, hu, hst, hsu, htcard, hucard, htu⟩ :=
      hpair s hs hsfacet ⟨x, intrinsicInterior_subset hxs, hxU⟩
    exact K.mem_interior_space_of_paired_facet hsfacet ht hu htcard hucard hst hsu htu hxs

theorem mem_interior_space_of_paired_facets_at (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces,
      s ⊆ t ∧ t.card = Module.finrank ℝ E + 1)
    {x : E} (hx : x ∈ K.space)
    (hpair : ∀ s ∈ K.faces, s.card = Module.finrank ℝ E →
      x ∈ convexHull ℝ (s : Set E) → K.HasTwoFullCofaces (Module.finrank ℝ E) s) :
    x ∈ interior K.space := by
  classical
  let T := hfinite.toFinset.filter (fun s => s.card = Module.finrank ℝ E ∧
    ¬K.HasTwoFullCofaces (Module.finrank ℝ E) s)
  let B : Set E := ⋃ s ∈ T, convexHull ℝ (s : Set E)
  have hB : IsClosed B :=
    (T.finite_toSet.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp h
    obtain ⟨hsK, hcard, hnot⟩ := Finset.mem_filter.mp hs
    exact hnot (hpair s (hfinite.mem_toFinset.mp hsK) hcard hxs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hxB)
  have hcover : Metric.ball x r ⊆ K.space := by
    apply K.covers_convex_open_of_paired_facets hfinite hpure Metric.isOpen_ball
      (convex_ball x r) ⟨x, Metric.mem_ball_self hr, hx⟩
    intro s hs hcard hmeet
    by_contra hnot
    obtain ⟨y, hyface, hyball⟩ := hmeet
    apply hball hyball
    exact mem_iUnion₂.mpr ⟨s,
      Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hs, hcard, hnot⟩, hyface⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hcover)

end Geometry.SimplicialComplex

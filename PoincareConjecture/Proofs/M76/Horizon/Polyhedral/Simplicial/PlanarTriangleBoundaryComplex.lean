import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaries
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_planar_triangle_boundary_complex (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) {t : Finset E}
    (ht : t ∈ K.faces) (hcard : t.card = 3) :
    ∃ J : SimplicialComplex ℝ E,
      J.faces.Finite ∧ J ≤ K ∧ J.space = frontier (convexHull ℝ (t : Set E)) ∧
      (∀ s : Finset E, s ∈ J.faces ↔ s.Nonempty ∧ ∃ p : t, s ⊆ t.erase p) ∧
      (∀ s ∈ J.faces, s.card ≤ 2) ∧
      ∀ p : t, t.erase p ∈ J.faces := by
  classical
  let edge (p : t) : K.faces :=
    ⟨t.erase p, (K.triangle_erase_is_edge ht hcard p.property).1⟩
  let A : Finset K.faces := Finset.univ.image edge
  let J := K.finiteFaceSpan A
  have hfaces (s : Finset E) : s ∈ J.faces ↔ s.Nonempty ∧ ∃ p : t, s ⊆ t.erase p := by
    rw [K.finiteFaceSpan_faces]
    constructor
    · rintro ⟨hs, u, hu, hsu⟩
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨hs, p, hsu⟩
    · rintro ⟨hs, p, hsp⟩
      exact ⟨hs, edge p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hsp⟩
  have hedges (p : t) : t.erase p ∈ J.faces := by
    apply (hfaces _).mpr
    have hp := K.triangle_erase_is_edge ht hcard p.property
    exact ⟨K.nonempty_of_mem_faces hp.1, p, Finset.Subset.refl _⟩
  have hspace : J.space = frontier (convexHull ℝ (t : Set E)) := by
    rw [K.triangle_frontier_eq_iUnion_erase hdim ht hcard]
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨_, p, hsp⟩ := (hfaces s).mp hs
      exact mem_iUnion.mpr ⟨p, convexHull_mono hsp hxs⟩
    · intro hx
      obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
      exact J.convexHull_subset_space (hedges p) hxp
  refine ⟨J, K.finiteFaceSpan_finite A, K.finiteFaceSpan_le A, hspace, hfaces, ?_, hedges⟩
  intro s hs
  obtain ⟨_, p, hsp⟩ := (hfaces s).mp hs
  exact (Finset.card_le_card hsp).trans_eq (K.triangle_erase_is_edge ht hcard p.property).2.1

theorem triangle_frontier_subset_of_edge_carriers (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) {t : Finset E}
    (ht : t ∈ K.faces) (hcard : t.card = 3) {S : Set E}
    (hedges : ∀ a b : E, a ≠ b → {a, b} ∈ K.faces → segment ℝ a b ⊆ S) :
    frontier (convexHull ℝ (t : Set E)) ⊆ S := by
  rw [K.triangle_frontier_eq_iUnion_erase hdim ht hcard]
  intro x hx
  obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
  obtain ⟨he, hc, _⟩ := K.triangle_erase_is_edge ht hcard p.property
  obtain ⟨a, b, hab, habedge⟩ := Finset.card_eq_two.mp hc
  rw [habedge] at he hxp
  exact hedges a b hab he (by simpa only [Finset.coe_pair, convexHull_pair] using hxp)

end Geometry.SimplicialComplex

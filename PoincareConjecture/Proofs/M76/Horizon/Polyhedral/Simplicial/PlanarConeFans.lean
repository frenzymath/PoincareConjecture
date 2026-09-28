import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.ConeTriangleCofaces
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem base_face_card_le_two_of_planar_cone (K L : SimplicialComplex ℝ E)
    (hplanar : Module.finrank ℝ E = 2) {c : E} (hc : c ∉ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces)) :
    ∀ s ∈ K.faces, s.card ≤ 2 := by
  intro s hs
  have hcs := K.apex_notMem_base_face hc hs
  have hins : insert c s ∈ L.faces := (hfaces _).mpr
    ⟨Finset.insert_nonempty _ _, Or.inr (by simpa only [Finset.erase_insert hcs] using hs)⟩
  have hcard := (L.indep hins).card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hle : (insert c s).card ≤ Module.finrank ℝ E + 1 := by
    simpa only [Fintype.card_coe] using hcard
  rw [Finset.card_insert_of_notMem hcs, hplanar] at hle
  omega



theorem ncard_boundary_edges_of_planar_cone (K L : SimplicialComplex ℝ E)
    (hplanar : Module.finrank ℝ E = 2) (hL : L.faces.Finite)
    {c : E} (hc : c ∈ interior L.space) (hboundary : K.space ⊆ frontier L.space)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    {q : E} (hq : q ∈ K.vertices) :
    {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e}.ncard = 2 := by
  have hcK : c ∉ K.vertices := fun h => (hboundary (K.vertices_subset_space h)).2 hc
  have hcq : c ≠ q := fun h => hcK (h.symm ▸ hq)
  have hedge : ({c, q} : Finset E) ∈ L.faces := by
    apply (hfaces _).mpr
    refine ⟨by simp, Or.inr ?_⟩
    simpa [hcq, Ne.symm hcq] using (show ({q} : Finset E) ∈ K.faces from hq)
  have hecard : ({c, q} : Finset E).card = Module.finrank ℝ E := by
    rw [Finset.card_pair hcq, hplanar]
  have hcount := L.faceLink_ncard_eq_two_of_hull_meets_interior hL hedge hecard
    ⟨c, subset_convexHull ℝ (↑({c, q} : Finset E) : Set E) (by simp), hc⟩
  rw [L.ncard_faceLink_vertices_eq_cofaces, Finset.card_pair hcq] at hcount
  exact (K.ncard_cone_radial_triangle_cofaces L hcK hq hfaces
    (K.base_face_card_le_two_of_planar_cone L hplanar hcK hfaces)).symm.trans hcount



theorem exists_planar_cone_vertex_fan (K L : SimplicialComplex ℝ E)
    (hplanar : Module.finrank ℝ E = 2) (hL : L.faces.Finite)
    {c : E} (hc : c ∈ interior L.space) (hboundary : K.space ⊆ frontier L.space)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    {q : E} (hq : q ∈ K.vertices) :
    ∃ u v : E, q ≠ u ∧ q ≠ v ∧ u ≠ v ∧
      {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e} =
        {({q, u} : Finset E), {q, v}} ∧
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ q ∈ t} =
        {({q, c, u} : Finset E), {q, c, v}} ∧
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ ({c, q} : Finset E) ⊆ t}.ncard = 2 := by
  have hcK : c ∉ K.vertices := fun h => (hboundary (K.vertices_subset_space h)).2 hc
  exact K.exists_cone_vertex_fan_of_two_boundary_edges L hcK hq hfaces
    (K.base_face_card_le_two_of_planar_cone L hplanar hcK hfaces)
    (K.ncard_boundary_edges_of_planar_cone L hplanar hL hc hboundary hfaces hq)

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeMarks
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaryComplex
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_edge_intrinsicInterior_of_not_vertex (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {e : Finset E} (he : e ∈ K.faces) (hecard : e.card = 2)
    {q : E} (hqe : q ∈ convexHull ℝ (e : Set E)) (hqv : q ∉ K.vertices) :
    q ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E)) := by
  obtain ⟨s, hs, hqs⟩ := K.exists_face_intrinsicInterior_of_finite hK
    (K.convexHull_subset_space he hqe)
  have hse := K.subset_of_mem_intrinsicInterior_face hs he hqs hqe
  have hcpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hcle : s.card ≤ 2 := (Finset.card_le_card hse).trans_eq hecard
  have hcne : s.card ≠ 1 := by
    intro h
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
    have hqv' : q = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        (intrinsicInterior_subset hqs)
    exact hqv (hqv'.symm ▸ hs)
  have heq : s = e := Finset.eq_of_subset_of_card_le hse (by omega)
  exact heq ▸ hqs

variable [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_interior_skeleton_edge_cofaces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2) {q : E}
    (hqskel : q ∈ ⋃ e : {s : K.faces // s.val.card = 2},
      convexHull ℝ (e.val.val : Set E))
    (hqv : q ∉ K.vertices) (hqint : q ∈ interior K.space) :
    ∃ e : {s : K.faces // s.val.card = 2},
      q ∈ intrinsicInterior ℝ (convexHull ℝ (e.val.val : Set E)) ∧
      (∀ f : {s : K.faces // s.val.card = 2},
        q ∈ convexHull ℝ (f.val.val : Set E) → f = e) ∧
      ∃ s t : {s : K.faces // s.val.card = 3}, s ≠ t ∧
        e.val.val ⊆ s.val.val ∧ e.val.val ⊆ t.val.val ∧
        ∀ u : {s : K.faces // s.val.card = 3},
          e.val.val ⊆ u.val.val ↔ u = s ∨ u = t := by
  obtain ⟨e, hqe⟩ := mem_iUnion.mp hqskel
  have hqei := K.mem_edge_intrinsicInterior_of_not_vertex hK
    e.val.property e.property hqe hqv
  have hcount := K.faceLink_ncard_eq_two_of_hull_meets_interior hK e.val.property
    (e.property.trans hdim.symm) ⟨q, hqe, hqint⟩
  rw [K.ncard_faceLink_vertices_eq_cofaces, e.property] at hcount
  obtain ⟨s, t, hst, hset⟩ := Set.ncard_eq_two.mp hcount
  have hs : s ∈ K.faces ∧ s.card = 3 ∧ e.val.val ⊆ s := by
    have h : s ∈ {u : Finset E | u ∈ K.faces ∧ u.card = 2 + 1 ∧ e.val.val ⊆ u} := by
      rw [hset]
      simp
    exact h
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ e.val.val ⊆ t := by
    have h : t ∈ {u : Finset E | u ∈ K.faces ∧ u.card = 2 + 1 ∧ e.val.val ⊆ u} := by
      rw [hset]
      simp
    exact h
  refine ⟨e, hqei, ?_, ⟨⟨s, hs.1⟩, hs.2.1⟩, ⟨⟨t, ht.1⟩, ht.2.1⟩,
    ?_, hs.2.2, ht.2.2, ?_⟩
  · intro f hqf
    have hef := K.subset_of_mem_intrinsicInterior_face e.val.property f.val.property hqei hqf
    have heq : e.val.val = f.val.val := Finset.eq_of_subset_of_card_le hef
      (by rw [e.property, f.property])
    exact Subtype.ext (Subtype.ext heq.symm)
  · intro h
    exact hst (congrArg (fun z => z.val.val) h)
  · intro u
    constructor
    · intro heu
      have hu : u.val.val ∈ {v : Finset E | v ∈ K.faces ∧ v.card = 2 + 1 ∧ e.val.val ⊆ v} :=
        ⟨u.val.property, u.property, heu⟩
      rw [hset] at hu
      rcases hu with hu | hu
      · exact Or.inl (Subtype.ext (Subtype.ext hu))
      · exact Or.inr (Subtype.ext (Subtype.ext hu))
    · rintro (rfl | rfl)
      · exact hs.2.2
      · exact ht.2.2



theorem refined_triangle_boundary_edgeStar_eq (K R L Q : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) {e t : Finset E}
    (he : e ∈ K.faces) (hecard : e.card = 2)
    (ht : t ∈ K.faces) (htcard : t.card = 3) (het : e ⊆ t)
    (hLR : L ≤ R) (hQR : Q ≤ R)
    (hL : L.space = frontier (convexHull ℝ (t : Set E)))
    (hQ : Q.space = convexHull ℝ (e : Set E))
    {q : E} (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E))) :
    {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ q ∈ s} =
      {s : Finset E | s ∈ Q.faces ∧ s.card = 2 ∧ q ∈ s} := by
  obtain ⟨J, hJ, _, hJS, hJfaces, hJdim, _⟩ :=
    K.exists_planar_triangle_boundary_complex hdim ht htcard
  have hproper : e ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨het, by
    intro h
    have hh := congrArg Finset.card h
    omega⟩
  obtain ⟨p, hpt, hpe⟩ := Finset.exists_of_ssubset hproper
  have heJ : e ∈ J.faces := (hJfaces e).mpr
    ⟨K.nonempty_of_mem_faces he, ⟨p, hpt⟩, fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hpe (by simpa only [h] using hx), het hx⟩⟩
  exact J.retained_edge_edgeStar_eq R L Q hJ hJdim hLR hQR
    (hL.trans hJS.symm) heJ hecard hQ hq



theorem exists_interior_skeleton_shared_boundary_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (R : SimplicialComplex ℝ E)
    (L : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (hLR : ∀ s, L s ≤ R)
    (hL : ∀ s, (L s).space = frontier (convexHull ℝ (s.val.val : Set E)))
    (Q : {s : K.faces // s.val.card = 2} → SimplicialComplex ℝ E)
    (hQR : ∀ s, Q s ≤ R)
    (hQ : ∀ s, (Q s).space = convexHull ℝ (s.val.val : Set E))
    {q : E} (hqskel : q ∈ ⋃ e : {s : K.faces // s.val.card = 2},
      convexHull ℝ (e.val.val : Set E))
    (hqv : q ∉ K.vertices) (hqint : q ∈ interior K.space) :
    ∃ e : {s : K.faces // s.val.card = 2},
      q ∈ intrinsicInterior ℝ (convexHull ℝ (e.val.val : Set E)) ∧
      (∀ f : {s : K.faces // s.val.card = 2},
        q ∈ convexHull ℝ (f.val.val : Set E) → f = e) ∧
      ∃ s t : {s : K.faces // s.val.card = 3}, s ≠ t ∧
        e.val.val ⊆ s.val.val ∧ e.val.val ⊆ t.val.val ∧
        (∀ u : {s : K.faces // s.val.card = 3},
          e.val.val ⊆ u.val.val ↔ u = s ∨ u = t) ∧
        ∀ u : {s : K.faces // s.val.card = 3}, e.val.val ⊆ u.val.val →
          {r : Finset E | r ∈ (L u).faces ∧ r.card = 2 ∧ q ∈ r} =
            {r : Finset E | r ∈ (Q e).faces ∧ r.card = 2 ∧ q ∈ r} := by
  obtain ⟨e, hqe, heunique, s, t, hst, hes, het, hcofaces⟩ :=
    K.exists_interior_skeleton_edge_cofaces hK hdim hqskel hqv hqint
  refine ⟨e, hqe, heunique, s, t, hst, hes, het, hcofaces, ?_⟩
  intro u heu
  exact K.refined_triangle_boundary_edgeStar_eq R (L u) (Q e) hdim
    e.val.property e.property u.val.property u.property heu
    (hLR u) (hQR e) (hL u) (hQ e) hqe

end Geometry.SimplicialComplex

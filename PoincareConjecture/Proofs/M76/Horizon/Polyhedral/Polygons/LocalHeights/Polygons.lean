import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.MarkedDegrees
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.CrossingDegrees
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Carrier
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Intersections
import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_triangleSlice_polygons_of_marked_fans (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (hK : K.faces.Finite)
    (hnozero : ∀ e ∈ K.faces, e.card = 2 → ∃ q ∈ e, q ∉ K.triangleZeroVertices A)
    (hcofaces : ∀ e : K.triangleCrossingEdges A,
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}.ncard = 2)
    (hfans : ∀ q : K.triangleZeroVertices A, ∃ a b u v : E,
      ({q.val, a, u} : Finset E) ∈ K.faces ∧ ({q.val, a, u} : Finset E).card = 3 ∧
      ({q.val, a, v} : Finset E) ∈ K.faces ∧ ({q.val, a, v} : Finset E).card = 3 ∧
      ({q.val, b, u} : Finset E) ∈ K.faces ∧ ({q.val, b, u} : Finset E).card = 3 ∧
      ({q.val, b, v} : Finset E) ∈ K.faces ∧ ({q.val, b, v} : Finset E).card = 3 ∧
      (∀ t ∈ K.faces, t.card = 3 → q.val ∈ t →
        t = {q.val, a, u} ∨ t = {q.val, a, v} ∨ t = {q.val, b, u} ∨ t = {q.val, b, v}) ∧
      a ≠ b ∧
      A {q.val, a, u} a ≠ 0 ∧ A {q.val, a, u} a = A {q.val, a, v} a ∧
      A {q.val, b, u} b ≠ 0 ∧ A {q.val, b, u} b = A {q.val, b, v} b ∧
      A {q.val, a, u} u < 0 ∧ 0 < A {q.val, a, v} v ∧
      A {q.val, b, u} u < 0 ∧ 0 < A {q.val, b, v} v) :
    ∃ (n : (K.triangleSliceGraph A).ConnectedComponent → ℕ)
      (P : ∀ C, Polygon E (n C + 3)),
      (∀ C, Function.Injective (P C) ∧ (P C).HasSimplicialEdges) ∧
      K.triangleZeroSet A = ⋃ C, (P C).boundary ℝ ∧
      Pairwise (fun C D => Disjoint ((P C).boundary ℝ) ((P D).boundary ℝ)) := by
  classical
  have hvertices : K.vertices.Finite := hK.preimage Finset.singleton_injective.injOn
  have hzeros : (K.triangleZeroVertices A).Finite := hvertices.subset (fun _ hq => hq.1)
  let : Finite (K.triangleZeroVertices A) := hzeros.to_subtype
  let : Finite (K.triangleCrossingEdges A) := (K.finite_triangleCrossingEdges A hK).to_subtype
  have hdegree : ∀ w : K.TriangleSliceLabel A,
      ((K.triangleSliceGraph A).neighborSet w).ncard = 2 := by
    intro w
    cases w with
    | inl q =>
      obtain ⟨a, b, u, v, hau, hauc, hav, havc, hbu, hbuc, hbv, hbvc,
        htriangles, hab, ha, haa, hb, hbb, hua, hva, hub, hvb⟩ := hfans q
      obtain ⟨e, f, hef, hpair⟩ := K.triangleSliceGraph_marked_neighbor_pair hA q.property
        hau hauc hav havc hbu hbuc hbv hbvc htriangles hab ha haa hb hbb hua hva hub hvb
      have hset : (K.triangleSliceGraph A).neighborSet (.inl q) =
          ({.inr e, .inr f} : Set (K.TriangleSliceLabel A)) := by
        ext w
        exact hpair w
      rw [hset]
      exact ncard_pair (fun h => hef (Sum.inr.inj h))
    | inr e => exact K.triangleSliceGraph_crossing_two_neighbors hA hcofaces e
  have hcover : K.triangleZeroSet A =
      (K.triangleSliceGraph A).segmentCarrier (K.triangleSlicePoint A) := by
    rw [K.triangleSliceGraph_carrier hA hnozero]
    apply union_eq_right.mpr
    intro q hq
    have hnonempty : ((K.triangleSliceGraph A).neighborSet (.inl ⟨q, hq⟩)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hdegree]; decide)
    obtain ⟨w, hw⟩ := hnonempty
    exact ⟨.inl ⟨q, hq⟩, w, hw, left_mem_segment ℝ q _⟩
  obtain ⟨n, P, hP, hboundary, hdisjoint⟩ :=
    (K.triangleSliceGraph A).exists_component_polygons_of_two_neighbors
      (K.triangleSlicePoint A) hdegree (K.triangleSlicePoint_injective A)
      (fun {_ _ _ _} hab hcd => K.triangleSliceGraph_segment_inter hA hab hcd)
  exact ⟨n, P, fun C => ⟨(hP C).1, (hP C).2.1⟩, hcover.trans hboundary, hdisjoint⟩

end Geometry.SimplicialComplex

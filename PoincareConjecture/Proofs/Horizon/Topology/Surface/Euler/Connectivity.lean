import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.ConnectedCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Cells
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Interior
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.Euler

open PoincareConjecture.Surface.Combinatorial.Incidence

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [PreconnectedSpace M] {I : Type v} [Finite I]

theorem endpointConnected_faces (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hcarrier : ∀ i, (face i).carrier = coordinates i '' convexHull ℝ (range (basis i)))
    (hcover : (⋃ i, (face i).carrier) = univ)
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {coordinates i (basis i w)})
    (adjacent : FaceBoundaryEdge face → I × I)
    (hexact : ∀ e i, (∃ k, faceBoundaryIndex face i k = e) ↔
      i = (adjacent e).1 ∨ i = (adjacent e).2) :
    EndpointConnected adjacent := by
  let V : Set M := range (fun p : I × Fin 3 => coordinates p.1 (basis p.1 p.2))
  have hV : V.Finite := finite_range _
  have hne (i : I) : (Vᶜ ∩ (face i).carrier).Nonempty := by
    have hni : (interior (face i).carrier).Nonempty := by
      rw [hcarrier i]
      exact coordinate_triangle_interior_nonempty (coordinates i) (basis i) (hsource i)
    obtain ⟨p, hpi, hpV⟩ := (dense_compl_finite hV).inter_open_nonempty
      _ isOpen_interior hni
    exact ⟨p, hpV, interior_subset hpi⟩
  intro i j
  have hchain := eqvGen_of_finite_closed_cover (isPreconnected_compl_finite hV)
    (fun i => (face i).carrier) (fun i => (face i).isClosed_carrier)
    (by rw [hcover]; exact subset_univ _) hne i j
  induction hchain with
  | refl i => exact Relation.EqvGen.refl i
  | symm i j h ih => exact ih.symm
  | trans i j k hij hjk ihij ihjk => exact Relation.EqvGen.trans _ _ _ ihij ihjk
  | rel i j h =>
    by_cases hij : i = j
    · subst j
      exact Relation.EqvGen.refl i
    obtain ⟨p, hpV, hpi, hpj⟩ := h
    rcases hinter i j hij with ⟨k, l, _, hkl⟩ | ⟨w, hw⟩
    · let e := faceBoundaryIndex face i k
      have hi := (hexact e i).mp ⟨k, rfl⟩
      have hj := (hexact e j).mp
        ⟨l, ((faceBoundaryIndex_eq_iff face i j k l).mpr hkl).symm⟩
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (hij (hi.trans hj.symm)).elim
      · exact Relation.EqvGen.rel i j ⟨e, Prod.ext hi.symm hj.symm⟩
      · exact (Relation.EqvGen.rel j i ⟨e, Prod.ext hj.symm hi.symm⟩).symm
      · exact (hij (hi.trans hj.symm)).elim
    · exact (hpV ⟨(i, w), (mem_singleton_iff.mp (hw ⟨hpi, hpj⟩)).symm⟩).elim

end PoincareConjecture.Topology.Surface.Euler

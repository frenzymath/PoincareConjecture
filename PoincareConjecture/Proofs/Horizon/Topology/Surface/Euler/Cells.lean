import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.BoundaryMaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates








set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.Euler

universe u v

variable {M : Type u} [TopologicalSpace M] {I : Type v}


def CoordinateVertex
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :=
  range (fun p : I × Fin 3 => coordinates p.1 (basis p.1 p.2))

instance [Finite I]
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    Finite (CoordinateVertex coordinates basis) :=
  (finite_range (fun p : I × Fin 3 => coordinates p.1 (basis p.1 p.2))).to_subtype


def coordinateCorner
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (i : I) (k : Fin 3) : CoordinateVertex coordinates basis :=
  ⟨coordinates i (basis i k), ⟨(i, k), rfl⟩⟩

theorem coordinateCorner_surjective
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    Function.Surjective (fun p : I × Fin 3 => coordinateCorner coordinates basis p.1 p.2) := by
  rintro ⟨p, ⟨⟨i, k⟩, rfl⟩⟩
  exact ⟨(i, k), rfl⟩

theorem coordinateCorner_injective
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source) (i : I) :
    Function.Injective (coordinateCorner coordinates basis i) := by
  intro k l h
  apply (basis i).ind.injective
  exact (coordinates i).injOn
    (hsource i (subset_convexHull ℝ _ (mem_range_self k)))
    (hsource i (subset_convexHull ℝ _ (mem_range_self l))) (congrArg Subtype.val h)

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]


noncomputable def coordinateEdgeEnds (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (e : FaceBoundaryEdge face) : CoordinateVertex coordinates basis × CoordinateVertex coordinates basis :=
  (coordinateCorner coordinates basis e.out.1 (e.out.2.succAbove 0),
    coordinateCorner coordinates basis e.out.1 (e.out.2.succAbove 1))

theorem coordinateEdgeEnds_distinct (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (e : FaceBoundaryEdge face) :
    (coordinateEdgeEnds face coordinates basis e).1 ≠
      (coordinateEdgeEnds face coordinates basis e).2 := by
  intro h
  have h01 := Fin.succAbove_right_injective
    (coordinateCorner_injective coordinates basis hsource e.out.1 h)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

end PoincareConjecture.Topology.Surface.Euler

import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Quotient

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {I : Type v}

def faceBoundarySetoid (face : I → SmoothFace M) : Setoid (I × Fin 3) :=
  Setoid.ker (fun p => ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1)

def FaceBoundaryEdge (face : I → SmoothFace M) := Quotient (faceBoundarySetoid face)

instance [Finite I] (face : I → SmoothFace M) : Finite (FaceBoundaryEdge face) :=
  inferInstanceAs (Finite (Quotient (faceBoundarySetoid face)))

def faceBoundaryIndex (face : I → SmoothFace M) (i : I) (k : Fin 3) :
    FaceBoundaryEdge face := Quotient.mk _ (i, k)

noncomputable def faceBoundaryEdge (face : I → SmoothFace M) (e : FaceBoundaryEdge face) :
    SmoothEdge M := (face e.out.1).boundary e.out.2

theorem faceBoundaryIndex_eq_iff (face : I → SmoothFace M) (i j : I) (k l : Fin 3) :
    faceBoundaryIndex face i k = faceBoundaryIndex face j l ↔
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((face j).boundary l).map '' Icc (0 : ℝ) 1 := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := faceBoundarySetoid face) h

theorem faceBoundaryEdge_image (face : I → SmoothFace M) (i : I) (k : Fin 3) :
    (faceBoundaryEdge face (faceBoundaryIndex face i k)).map '' Icc (0 : ℝ) 1 =
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 :=
  Setoid.ker_apply_mk_out
    (f := fun p : I × Fin 3 => ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1) (i, k)

noncomputable def normalizeFaceBoundary (face : I → SmoothFace M) (i : I) : SmoothFace M where
  map := (face i).map
  source := (face i).source
  source_compact := (face i).source_compact
  source_triangle := (face i).source_triangle
  smooth := (face i).smooth
  carrier := (face i).carrier
  carrier_eq_image := (face i).carrier_eq_image
  chart := (face i).chart
  carrier_subset_chart := (face i).carrier_subset_chart
  boundary k := faceBoundaryEdge face (faceBoundaryIndex face i k)
  boundary_carrier := by
    simp only [faceBoundaryEdge_image]
    exact (face i).boundary_carrier

@[simp] theorem normalizeFaceBoundary_map (face : I → SmoothFace M) (i : I) :
    (normalizeFaceBoundary face i).map = (face i).map := rfl

@[simp] theorem normalizeFaceBoundary_source (face : I → SmoothFace M) (i : I) :
    (normalizeFaceBoundary face i).source = (face i).source := rfl

@[simp] theorem normalizeFaceBoundary_carrier (face : I → SmoothFace M) (i : I) :
    (normalizeFaceBoundary face i).carrier = (face i).carrier := rfl

theorem normalizeFaceBoundary_boundary (face : I → SmoothFace M) (i : I) (k : Fin 3) :
    (normalizeFaceBoundary face i).boundary k =
      faceBoundaryEdge face (faceBoundaryIndex face i k) := rfl

theorem normalizeFaceBoundary_shared_edge (face : I → SmoothFace M) (i j : I) (k l : Fin 3)
    (h : ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
      ((face j).boundary l).map '' Icc (0 : ℝ) 1) :
    (normalizeFaceBoundary face i).boundary k = (normalizeFaceBoundary face j).boundary l := by
  simp only [normalizeFaceBoundary_boundary, (faceBoundaryIndex_eq_iff face i j k l).mpr h]

end PoincareConjecture.Topology.Surface

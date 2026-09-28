import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

set_option autoImplicit false

open Set
open scoped Convex Pointwise Topology

namespace PoincareConjecture.Topology.Surface

noncomputable section

private def basisTriangle
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
  ⟨b, b.ind⟩

private lemma basisTriangle_interior_eq_topological
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    (basisTriangle b).interior =
      interior (convexHull ℝ (Set.range b)) := by
  ext x
  constructor
  · rintro ⟨w, hw, hwI, hwx⟩
    rw [AffineBasis.interior_convexHull]
    intro i
    rw [← hwx]
    change 0 < b.coord i (Finset.univ.affineCombination ℝ b w)
    rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) hw]
    exact (hwI i).1
  · intro hx
    rw [AffineBasis.interior_convexHull] at hx
    refine ⟨fun i => b.coord i x, b.sum_coord_apply_eq_one x, ?_,
      b.affineCombination_coord_eq_self x⟩
    intro i
    exact ⟨hx i, by
      rw [← b.sum_coord_apply_eq_one x]
      obtain ⟨j, hji⟩ := exists_ne i
      exact Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
        (hx j) (fun k _ _ => (hx k).le)⟩

private theorem frontier_convexHull_affineBasis_fin3
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    frontier (convexHull ℝ (Set.range b)) =
      ⋃ i : Fin 3,
        convexHull ℝ (Set.range ((basisTriangle b).faceOpposite i).points) := by
  let s := basisTriangle b
  have hsclosed : IsClosed (convexHull ℝ (Set.range b)) := by
    exact (Set.finite_range b).isClosed_convexHull ℝ
  calc
    _ = convexHull ℝ (Set.range b) \ interior (convexHull ℝ (Set.range b)) :=
      hsclosed.frontier_eq
    _ = s.closedInterior \ s.interior := by
      rw [show s.interior = interior (convexHull ℝ (Set.range b)) from
        basisTriangle_interior_eq_topological b,
        ← Affine.Simplex.convexHull_eq_closedInterior s]
      rfl
    _ = ⋃ i : Fin 3, (s.faceOpposite i).closedInterior :=
      s.closedInterior_sdiff_interior
    _ = _ := by simp only [Affine.Simplex.convexHull_eq_closedInterior]; rfl

theorem frontier_convexHull_affineBasis_fin3_segments
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    frontier (convexHull ℝ (Set.range b)) =
      ⋃ i : Fin 3,
        affineSegment ℝ (b (Fin.succAbove i 0)) (b (Fin.succAbove i 1)) := by
  rw [frontier_convexHull_affineBasis_fin3 b]
  congr 1
  funext i
  rw [Affine.Simplex.convexHull_eq_closedInterior,
    Affine.Simplex.closedInterior_eq_affineSegment]
  simp [basisTriangle, Affine.Simplex.faceOpposite_point_eq_point_succAbove]

theorem frontier_convexHull_affineBasis_fin3_image
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    frontier (convexHull ℝ (Set.range b)) =
      ⋃ i : Fin 3,
        (fun t : ℝ => b (Fin.succAbove i 0) +
          t • (b (Fin.succAbove i 1) - b (Fin.succAbove i 0))) '' Icc (0 : ℝ) 1 := by
  rw [frontier_convexHull_affineBasis_fin3_segments]
  simp only [affineSegment]
  congr 1
  funext i
  congr 1
  funext t
  simp [AffineMap.lineMap_apply, vadd_eq_add]
  abel

end

end PoincareConjecture.Topology.Surface

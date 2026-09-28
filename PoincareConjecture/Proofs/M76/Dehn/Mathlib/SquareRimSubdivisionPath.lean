import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.UniformPolygonCorrespondence
import PoincareConjecture.Proofs.M76.Wall.SquareRimCoordinates










set_option autoImplicit false

open Set Metric Geometry Polygon
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)



theorem squareRimLoop_quarter (i : Fin 4) (s : unitInterval) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hs : 4 * (s : ℝ) = (i : ℝ) + u) :
    (squareRimLoop s : V2) =
      AffineMap.lineMap (squareRimPolygon i) (squareRimPolygon (finRotate 4 i)) u := by
  rw [Wall.squareRimLoop_coordinates]
  fin_cases i <;> norm_num at hs
  all_goals
    split_ifs <;> ext k <;> fin_cases k <;>
      norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
        AffineMap.lineMap_apply_module] <;> linarith [hu.1, hu.2]




theorem squareRimLoop_uniform_subedge (m : ℕ) (k : Fin (4 * (m + 1)))
    (a s : unitInterval)
    (ht : 4 * (m + 1 : ℝ) * (s : ℝ) = (k : ℝ) + (a : ℝ)) :
    let U := squareRimPolygon.subdivide (uniformEdgeParameters m)
    (squareRimLoop s : V2) =
      AffineMap.lineMap (U k) (U (finRotate (4 * (m + 1)) k)) (a : ℝ) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hden : (0 : ℝ) < m + 1 := by positivity
  have hj : (j : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hj0 : (0 : ℝ) ≤ j := by positivity
  let u : ℝ := ((j : ℝ) + (a : ℝ)) / (m + 1 : ℝ)
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [a.property.1]) hden.le, ?_⟩
    exact (div_le_one hden).mpr (by linarith [a.property.2])
  have ht' : 4 * (m + 1 : ℝ) * (s : ℝ) =
      (j : ℝ) + (m + 1 : ℝ) * (i : ℝ) + (a : ℝ) := by
    simpa only [finProdFinEquiv_apply_val, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using ht
  have hs : 4 * (s : ℝ) = (i : ℝ) + u := by
    dsimp [u]
    field_simp
    nlinarith [ht']
  change (squareRimLoop s : V2) =
    AffineMap.lineMap
      (squareRimPolygon.subdivide (uniformEdgeParameters m) (finProdFinEquiv (i, j)))
      (squareRimPolygon.subdivide (uniformEdgeParameters m)
        (finRotate (4 * (m + 1)) (finProdFinEquiv (i, j)))) (a : ℝ)
  rw [squareRimPolygon.subdivide_apply,
    squareRimPolygon.subdivide_rotate_apply _ (uniformEdgeParameters_zero m)
      (uniformEdgeParameters_last m), ← AffineMap.apply_lineMap]
  have hparam : AffineMap.lineMap (uniformEdgeParameters m j.castSucc)
      (uniformEdgeParameters m j.succ) (a : ℝ) = u := by
    simp only [uniformEdgeParameters, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, AffineMap.lineMap_apply_module, smul_eq_mul]
    dsimp [u]
    ring
  rw [hparam]
  exact squareRimLoop_quarter i s hu hs

end PoincareConjecture.M76.Dehn

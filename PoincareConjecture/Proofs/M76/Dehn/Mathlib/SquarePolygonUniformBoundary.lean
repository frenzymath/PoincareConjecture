import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquarePolygonBoundaryCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimSubdivisionPath










set_option autoImplicit false

open Set Metric Geometry Polygon
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1




theorem exists_square_polygon_uniform_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ e : Q ≃ₜ P.boundary ℝ, e.IsFinitePL ∧ (e squareRimBase : E) = P 0 ∧
      ∀ (i : Fin (n + 3)) (u s : unitInterval),
        (n + 3 : ℝ) * (s : ℝ) = (i : ℝ) + (u : ℝ) →
        (e (squareRimLoop s) : E) =
          AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) (u : ℝ) := by
  obtain ⟨e, he, hbase, hcoord⟩ := exists_square_polygon_boundary_coordinates P hP hinj
  refine ⟨e, he, hbase, ?_⟩
  intro i u s hs
  have hu : (u : ℝ) ∈ Icc (uniformEdgeParameters 3 0)
      (uniformEdgeParameters 3 (Fin.last 4)) := by
    simpa only [uniformEdgeParameters_zero, uniformEdgeParameters_last] using u.property
  obtain ⟨j, hj⟩ := (strictMono_uniformEdgeParameters 3).monotone.exists_mem_consecutive_Icc hu
  have hj' : (j : ℝ) / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ ((j : ℝ) + 1) / 4 := by
    simpa only [Set.mem_Icc, uniformEdgeParameters, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (3 : ℝ) + 1 = 4 from by norm_num] using hj
  let a : unitInterval := ⟨4 * (u : ℝ) - (j : ℝ),
    ⟨by linarith [hj'.1], by linarith [hj'.2]⟩⟩
  let hsize : 4 * (n + 3) = (n + 3) * 4 := Nat.mul_comm _ _
  let k : Fin (4 * (n + 3)) := Fin.cast hsize.symm (finProdFinEquiv (i, j))
  have hkv : (k : ℝ) = (j : ℝ) + 4 * (i : ℝ) := by
    change ((finProdFinEquiv (i, j)).val : ℝ) = (j : ℝ) + 4 * (i : ℝ)
    norm_num [finProdFinEquiv_apply_val, Nat.cast_add, Nat.cast_mul]
  have htime : 4 * (((n + 2 : ℕ) : ℝ) + 1) * (s : ℝ) = (k : ℝ) + (a : ℝ) := by
    rw [hkv]
    change 4 * (((n + 2 : ℕ) : ℝ) + 1) * (s : ℝ) =
      (j : ℝ) + 4 * (i : ℝ) + (4 * (u : ℝ) - (j : ℝ))
    push_cast
    nlinarith [hs]
  have hrho := squareRimLoop_uniform_subedge (n + 2) k a s htime
  let U := squareRimPolygon.subdivide (uniformEdgeParameters (n + 2))
  have hpoint : AffineMap.lineMap (U k) (U (finRotate (4 * (n + 3)) k)) (a : ℝ) ∈ Q :=
    hrho ▸ (squareRimLoop s).property
  have hsame : (⟨AffineMap.lineMap (U k) (U (finRotate (4 * (n + 3)) k)) (a : ℝ),
      hpoint⟩ : Q) = squareRimLoop s := Subtype.ext hrho.symm
  have hv := hcoord k (a : ℝ) a.property hpoint
  rw [hsame] at hv
  have hcast : Fin.cast hsize k = finProdFinEquiv (i, j) := by
    apply Fin.ext
    rfl
  rw [hcast, P.subdivide_apply,
    P.subdivide_rotate_apply _ (uniformEdgeParameters_zero 3)
      (uniformEdgeParameters_last 3), ← AffineMap.apply_lineMap] at hv
  have hparameter : AffineMap.lineMap (uniformEdgeParameters 3 j.castSucc)
      (uniformEdgeParameters 3 j.succ) (a : ℝ) = (u : ℝ) := by
    simp only [uniformEdgeParameters, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, AffineMap.lineMap_apply_module, smul_eq_mul]
    dsimp [a]
    ring
  rw [hparameter] at hv
  exact hv

end PoincareConjecture.M76.Dehn

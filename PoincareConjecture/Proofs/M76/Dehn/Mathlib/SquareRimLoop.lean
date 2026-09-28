import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Metric
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

def squareRimVertex (i : Fin 4) : Q :=
  ⟨![![-1, -1], ![1, -1], ![1, 1], ![-1, 1]] i, by
    apply mem_sphere_zero_iff_norm.mpr
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro j
      fin_cases i <;> fin_cases j <;> norm_num
    · have h := norm_le_pi_norm
        (![![-1, -1], ![1, -1], ![1, 1], ![-1, 1]] i : V2) 0
      fin_cases i <;> simpa using h⟩

def squareRimBase : Q := squareRimVertex 0

private theorem segment_mem_squareRim (a b : Q) (k : Fin 2)
    (hfixed : a.val k = b.val k) (hunit : ‖a.val k‖ = 1)
    (t : unitInterval) : Path.segment a.val b.val t ∈ Q := by
  have hsegment : Path.segment a.val b.val t ∈ segment ℝ a.val b.val := by
    rw [← Path.range_segment]
    exact mem_range_self t
  have hball := (convex_closedBall (0 : V2) 1).segment_subset
    (sphere_subset_closedBall a.property) (sphere_subset_closedBall b.property) hsegment
  have hle : ‖Path.segment a.val b.val t‖ ≤ 1 := mem_closedBall_zero_iff.mp hball
  have hcoordinate : Path.segment a.val b.val t k = a.val k := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfixed]
    ring
  have hge := norm_le_pi_norm (Path.segment a.val b.val t) k
  rw [hcoordinate, hunit] at hge
  exact mem_sphere_zero_iff_norm.mpr (le_antisymm hle hge)

private noncomputable def squareRimSegment (a b : Q) (k : Fin 2)
    (hfixed : a.val k = b.val k) (hunit : ‖a.val k‖ = 1) : Path a b where
  toFun t := ⟨Path.segment a.val b.val t, segment_mem_squareRim a b k hfixed hunit t⟩
  continuous_toFun := (Path.segment a.val b.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment a.val b.val).source
  target' := Subtype.ext (Path.segment a.val b.val).target

noncomputable def squareRimEdge (i : Fin 4) :
    Path (squareRimVertex i) (squareRimVertex (i + 1)) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact squareRimSegment _ _ 1 (by rfl) (by norm_num [squareRimVertex])
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact squareRimSegment _ _ 0 (by rfl) (by norm_num [squareRimVertex])
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact squareRimSegment _ _ 1 (by rfl) (by change ‖(1 : ℝ)‖ = 1; norm_num)
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        exact squareRimSegment _ _ 0 (by rfl) (by change ‖(-1 : ℝ)‖ = 1; norm_num)

noncomputable def squareRimLoop : Path squareRimBase squareRimBase :=
  ((squareRimEdge 0).trans (squareRimEdge 1)).trans
    ((squareRimEdge 2).trans (squareRimEdge 3))

end PoincareConjecture.M76.Dehn

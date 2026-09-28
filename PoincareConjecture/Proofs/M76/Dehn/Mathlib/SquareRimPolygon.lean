import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop
import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

def squareRimPolygon : Polygon V2 4 :=
  ⟨fun i => (squareRimVertex i : V2)⟩

private theorem mem_squareRim_iff (x : V2) :
    x ∈ Q ↔ (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ ∃ i, x i = -1 ∨ x i = 1 := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro hx
    have hb (i : Fin 2) : ‖x i‖ ≤ 1 := hx ▸ norm_le_pi_norm x i
    refine ⟨fun i => abs_le.mp (hb i), ?_⟩
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
    rw [hx] at hi
    refine ⟨i, ?_⟩
    change |x i| = 1 at hi
    rcases le_total 0 (x i) with h | h
    · rw [abs_of_nonneg h] at hi
      exact Or.inr hi
    · rw [abs_of_nonpos h] at hi
      exact Or.inl (by linarith)
  · rintro ⟨hb, i, hi⟩
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
        (fun i => abs_le.mpr (hb i))
    · have hn := norm_le_pi_norm x i
      rcases hi with hi | hi <;> simpa only [hi, norm_neg, norm_one] using hn

theorem injective_squareRimPolygon : Function.Injective squareRimPolygon := by
  intro i j hij
  have hzero := congrFun hij 0
  have hone := congrFun hij 1
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | exfalso
      first
      | exact (show (-1 : ℝ) ≠ 1 by norm_num) hzero
      | exact (show (1 : ℝ) ≠ -1 by norm_num) hzero
      | exact (show (-1 : ℝ) ≠ 1 by norm_num) hone
      | exact (show (1 : ℝ) ≠ -1 by norm_num) hone

theorem hasSimplicialEdges_squareRimPolygon : squareRimPolygon.HasSimplicialEdges := by
  intro i j x hx
  by_cases hij : i = j
  · subst j
    rw [inter_self, ← squareRimPolygon.edgeSet_eq_convexHull]
    exact hx.1
  obtain ⟨a, ha, hax⟩ := hx.1
  obtain ⟨b, hb, hbx⟩ := hx.2
  have heq := hax.trans hbx.symm
  have hzero := congrFun heq 0
  have hone := congrFun heq 1
  rw [← hax]
  apply subset_convexHull ℝ _
  simp only [mem_inter_iff, Polygon.edgeVertices, Finset.coe_pair,
    mem_insert_iff, mem_singleton_iff]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
      AffineMap.lineMap_apply_module] at hzero hone
  all_goals try (exfalso; linarith [ha.1, ha.2, hb.1, hb.2])
  all_goals
    constructor <;>
      first
      | left
        ext k
        fin_cases k <;>
          norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
            AffineMap.lineMap_apply_module] <;> linarith
      | right
        ext k
        fin_cases k <;>
          norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
            AffineMap.lineMap_apply_module] <;> linarith

theorem boundary_squareRimPolygon : squareRimPolygon.boundary ℝ = Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hx
    apply (mem_squareRim_iff _).mpr
    constructor
    · intro k
      fin_cases i <;> fin_cases k <;> constructor <;>
        norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
          AffineMap.lineMap_apply_module] <;> linarith [ht.1, ht.2]
    · fin_cases i
      · refine ⟨1, Or.inl ?_⟩
        norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
          AffineMap.lineMap_apply_module]
        ring
      · refine ⟨0, Or.inr ?_⟩
        norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
          AffineMap.lineMap_apply_module]
      · refine ⟨1, Or.inr ?_⟩
        norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
          AffineMap.lineMap_apply_module]
      · refine ⟨0, Or.inl ?_⟩
        norm_num [squareRimPolygon, squareRimVertex, finRotate_apply, Fin.add_def,
          AffineMap.lineMap_apply_module]
        ring
  · intro hx
    obtain ⟨hb, i, hi⟩ := (mem_squareRim_iff x).mp hx
    apply mem_iUnion.mpr
    fin_cases i
    · rcases hi with hi | hi
      · refine ⟨(3 : Fin 4), (1 - x 1) / 2,
          ⟨by linarith [(hb 1).2], by linarith [(hb 1).1]⟩, ?_⟩
        change x 0 = -1 at hi
        change AffineMap.lineMap (![-1, 1] : V2) ![-1, -1] ((1 - x 1) / 2) = x
        ext k
        fin_cases k <;>
          norm_num [AffineMap.lineMap_apply_module] <;> linarith
      · refine ⟨(1 : Fin 4), (x 1 + 1) / 2,
          ⟨by linarith [(hb 1).1], by linarith [(hb 1).2]⟩, ?_⟩
        change x 0 = 1 at hi
        change AffineMap.lineMap (![1, -1] : V2) ![1, 1] ((x 1 + 1) / 2) = x
        ext k
        fin_cases k <;>
          norm_num [AffineMap.lineMap_apply_module] <;> linarith
    · rcases hi with hi | hi
      · refine ⟨(0 : Fin 4), (x 0 + 1) / 2,
          ⟨by linarith [(hb 0).1], by linarith [(hb 0).2]⟩, ?_⟩
        change x 1 = -1 at hi
        change AffineMap.lineMap (![-1, -1] : V2) ![1, -1] ((x 0 + 1) / 2) = x
        ext k
        fin_cases k <;>
          norm_num [AffineMap.lineMap_apply_module] <;> linarith
      · refine ⟨(2 : Fin 4), (1 - x 0) / 2,
          ⟨by linarith [(hb 0).2], by linarith [(hb 0).1]⟩, ?_⟩
        change x 1 = 1 at hi
        change AffineMap.lineMap (![1, 1] : V2) ![-1, 1] ((1 - x 0) / 2) = x
        ext k
        fin_cases k <;>
          norm_num [AffineMap.lineMap_apply_module] <;> linarith

end PoincareConjecture.M76.Dehn

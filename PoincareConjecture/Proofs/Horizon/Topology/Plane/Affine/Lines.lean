import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
open Set
open scoped Matrix

namespace Poincare.Topology.Plane

theorem exists_affine_line_containing_segment (p q : EuclideanSpace ℝ (Fin 2)) :
    ∃ l : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ,
      Function.Surjective l ∧ segment ℝ p q ⊆ {z | l z = 0} := by
  let coordinate (i : Fin 2) : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toAffineMap
  by_cases hx : q 0 = p 0
  · let l := coordinate 0 - AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) (p 0)
    refine ⟨l, ?_, ?_⟩
    · intro y
      refine ⟨WithLp.toLp 2 ![y + p 0, 0], ?_⟩
      simp [l, coordinate]
    · apply (convex_singleton (0 : ℝ)).affine_preimage l |>.segment_subset
      · simp [l, coordinate]
      · simp [l, coordinate, hx]
  · let m : ℝ := (q 1 - p 1) / (q 0 - p 0)
    let l := coordinate 1 - AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) (p 1) -
      m • (coordinate 0 - AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) (p 0))
    have hne : q 0 - p 0 ≠ 0 := sub_ne_zero.mpr hx
    refine ⟨l, ?_, ?_⟩
    · intro y
      refine ⟨WithLp.toLp 2 ![p 0, y + p 1], ?_⟩
      simp [l, coordinate]
    · apply (convex_singleton (0 : ℝ)).affine_preimage l |>.segment_subset
      · simp [l, coordinate]
      · simp [l, coordinate, m, div_mul_cancel₀ _ hne]

theorem exists_affine_lines_of_finite_segment_cover {I : Type*} [Finite I]
    (a b : I → EuclideanSpace ℝ (Fin 2)) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : s ⊆ ⋃ i, segment ℝ (a i) (b i)) :
    ∃ lines : List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧ s ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
  classical
  let := Fintype.ofFinite I
  choose l hl hcover using fun i => exists_affine_line_containing_segment (a i) (b i)
  refine ⟨Finset.univ.toList.map l, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact hl i
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hz)
    exact mem_iUnion.mpr ⟨l i, mem_iUnion.mpr
      ⟨List.mem_map.mpr ⟨i, by simp, rfl⟩, hcover i hi⟩⟩

theorem exists_affine_lines_iUnion {I : Type*} [Finite I]
    (s : I → Set (EuclideanSpace ℝ (Fin 2)))
    (h : ∀ i, ∃ lines : List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧ s i ⊆ ⋃ l ∈ lines, {z | l z = 0}) :
    ∃ lines : List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ), (∀ l ∈ lines, Function.Surjective l) ∧
      (⋃ i, s i) ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
  classical
  let := Fintype.ofFinite I
  choose lines hsurj hcover using h
  refine ⟨Finset.univ.toList.flatMap lines, ?_, ?_⟩
  · intro l hl
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hl
    exact hsurj i l hi
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcover i hi)
    obtain ⟨hl, hz⟩ := mem_iUnion.mp hl
    exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr
      ⟨List.mem_flatMap.mpr ⟨i, by simp, hl⟩, hz⟩⟩

end Poincare.Topology.Plane

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

open Set

section Algebraic

variable {𝕜 ι E F : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

theorem AffineIndependent.linearIndependent_collapse_direction {v : ι → E}
    (hv : AffineIndependent 𝕜 v) {s : Set ι} (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan 𝕜 (v '' s)) (Q : E →ₗ[𝕜] F)
    (hker : Q.ker = (affineSpan 𝕜 (v '' s)).direction) :
    LinearIndependent 𝕜 (fun i : {i // i ∉ s} => Q (v i - p)) := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  let v0 : {i : ι // i ≠ i0} → E := fun i => v i - v i0
  have hv0 : LinearIndependent 𝕜 v0 := by
    simpa only [vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub 𝕜 v i0).mp hv
  let outer : {i // i ∉ s} → {i : ι // i ≠ i0} :=
    fun i => ⟨i.val, fun he => i.property (he ▸ hi0)⟩
  have hout : Function.Injective outer := by
    intro i j hij
    exact Subtype.ext (congrArg (fun z : {i : ι // i ≠ i0} => z.val) hij)
  let central : Set {i : ι // i ≠ i0} := {i | i.val ∈ s}
  have hd : Disjoint (range outer) central := by
    apply disjoint_left.mpr
    rintro _ ⟨i, rfl⟩ hi
    exact i.property hi
  have hdir : (affineSpan 𝕜 (v '' s)).direction =
      Submodule.span 𝕜 (v0 '' central) := by
    rw [direction_affineSpan, vectorSpan_image_eq_span_vsub_set_right_ne 𝕜 v hi0]
    congr 1
    rw [image_image]
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi.2⟩, hi.1, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.val, ⟨hi, i.property⟩, rfl⟩
  have hmap : LinearIndependent 𝕜 (Q ∘ (v0 ∘ outer)) := by
    apply (hv0.comp outer hout).map
    rw [hker, hdir, Set.range_comp]
    exact hv0.disjoint_span_image hd
  have hpa : Q (p - v i0) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact (affineSpan 𝕜 (v '' s)).vsub_mem_direction hp
      (mem_affineSpan 𝕜 (mem_image_of_mem v hi0))
  have he : (fun i : {i // i ∉ s} => Q (v i - p)) = Q ∘ (v0 ∘ outer) := by
    funext i
    change Q (v i - p) = Q (v i - v i0)
    have hvp : v i - p = (v i - v i0) - (p - v i0) := by abel
    rw [hvp, map_sub, hpa, sub_zero]
  rwa [he]

end Algebraic

section Orthogonal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AffineIndependent.linearIndependent_orthogonal_normal {v : ι → E}
    (hv : AffineIndependent ℝ v) {s : Set ι} (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan ℝ (v '' s)) :
    LinearIndependent ℝ (fun i : {i // i ∉ s} =>
      (affineSpan ℝ (v '' s)).directionᗮ.orthogonalProjectionOnto (v i - p)) := by
  apply hv.linearIndependent_collapse_direction hs hp
  exact Submodule.ker_orthogonalProjectionOnto.trans
    (Submodule.orthogonal_orthogonal _)

end Orthogonal

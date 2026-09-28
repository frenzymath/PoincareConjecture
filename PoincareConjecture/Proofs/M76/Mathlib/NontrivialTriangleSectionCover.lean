import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem iUnion_nontrivial_triangle_sections (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E}
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q})) :
    let ι := {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}
    (⋃ i : ι, convexHull ℝ (i.val : Set E) ∩ {x | A x = 0}) =
      K.space ∩ {x | A x = 0} := by
  classical
  let ι := {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
    ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}
  have hfinite : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}.Finite :=
    hK.subset fun _ hs => hs.1
  let : Fintype ι := hfinite.fintype
  let B : Set E := ⋃ i : ι, convexHull ℝ (i.val : Set E) ∩ {x | A x = 0}
  have hB : B ⊆ K.space ∩ {x | A x = 0} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨K.convexHull_subset_space i.property.1 hi.1, hi.2⟩
  have hpunctured : (K.space ∩ {x | A x = 0}) \ {q} ⊆ B := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1.1
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs
    have hxt : x ∈ convexHull ℝ (t : Set E) ∩ {x | A x = 0} :=
      ⟨convexHull_mono hst hxs, hx.1.2⟩
    let i : ι := ⟨t, ht, htc, x, hxt, hx.2⟩
    exact mem_iUnion.mpr ⟨i, hxt⟩
  have hclosed : IsClosed B := by
    apply isClosed_iUnion_of_finite
    intro i
    exact ((i.val.finite_toSet.isCompact_convexHull ℝ).inter_right
      (isClosed_eq A.continuous_of_finiteDimensional continuous_const)).isClosed
  have hqB : q ∈ B := (closure_minimal hpunctured hclosed) hq
  exact Subset.antisymm hB (fun x hx => by
    by_cases hxq : x = q
    · exact hxq.symm ▸ hqB
    · exact hpunctured ⟨hx, hxq⟩)

end Geometry.SimplicialComplex

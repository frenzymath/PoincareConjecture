import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarConeCarrier
import PoincareConjecture.Proofs.M76.Mathlib.LinearIndependentFaceRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_finite_truncatedStarBoundary_complex
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = K.truncatedStarBoundary L α β ∧
      ∀ s ∈ J.faces, LinearIndependent ℝ ((↑) : s → E) := by
  obtain ⟨J₀, hJ₀, hJ₀s⟩ := (K.closedStar 0).exists_finite_affineLevel_complex
    (finite_closedStar_faces hK 0) L.toAffineMap α
  obtain ⟨J₁, hJ₁, hJ₁s⟩ := (K.closedStar 0).exists_finite_affineLevel_complex
    (finite_closedStar_faces hK 0) L.toAffineMap β
  obtain ⟨U, hU, hUs⟩ := (K.link 0).exists_finite_affineSlab_complex
    (finite_link_faces hK 0) L.toAffineMap α β
  obtain ⟨J₂, hJ₂, hJ₂U, hJ₂K⟩ := U.exists_finite_refinement_of_space_subset
    (K.link 0) hU (finite_link_faces hK 0) (hUs.subset.trans inter_subset_left)
  have hJ₂s : J₂.space = (K.link 0).space ∩ {x | L x ∈ Icc α β} :=
    hJ₂U.space_eq.trans hUs
  have hlin₀ := J₀.linearIndependent_faces_of_linear_level L hα.ne
    (fun _ hx => (hJ₀s.subset hx).2)
  have hlin₁ := J₁.linearIndependent_faces_of_linear_level L hβ.ne'
    (fun _ hx => (hJ₁s.subset hx).2)
  have hlin₂ := J₂.linearIndependent_faces_of_face_containment (K.link 0)
    (fun _ hs => linearIndependent_of_mem_link_zero hs) hJ₂K
  let C : Option Bool → SimplicialComplex ℝ E
    | none => J₀
    | some false => J₁
    | some true => J₂
  have hC (i : Option Bool) : (C i).faces.Finite := by
    rcases i with _ | i
    · exact hJ₀
    · cases i
      · exact hJ₁
      · exact hJ₂
  have hlinC (i : Option Bool) :
      ∀ s ∈ (C i).faces, LinearIndependent ℝ ((↑) : s → E) := by
    rcases i with _ | i
    · exact hlin₀
    · cases i
      · exact hlin₁
      · exact hlin₂
  obtain ⟨J, hJ, hJs, hfaces⟩ := exists_finite_triangulation_iUnion C hC
  refine ⟨J, hJ, hJs.trans ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases i with _ | i
      · exact Or.inl (Or.inl (hJ₀s.subset hi))
      · cases i
        · exact Or.inl (Or.inr (hJ₁s.subset hi))
        · exact Or.inr (hJ₂s.subset hi)
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨none, hJ₀s.symm.subset hx⟩
      · exact mem_iUnion.mpr ⟨some false, hJ₁s.symm.subset hx⟩
      · exact mem_iUnion.mpr ⟨some true, hJ₂s.symm.subset hx⟩
  · intro s hs
    obtain ⟨i, t, ht, hst⟩ := hfaces s hs
    exact (J.indep hs).linearIndependent_of_convexHull_subset (hlinC i t ht) hst

end Geometry.SimplicialComplex

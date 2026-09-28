import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar
import PoincareConjecture.Proofs.M76.Mathlib.TangentSecantSaturation

set_option autoImplicit false

open Set
open scoped Pointwise Topology

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

def closedFaceStar (K : SimplicialComplex 𝕜 E) (s : Finset E) : SimplicialComplex 𝕜 E where
  faces := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
  indep ht := K.indep ht.1
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro u hut hu
    exact ⟨K.down_closed ht.1 hut hu,
      K.down_closed ht.2 (Finset.union_subset_union Subset.rfl hut)
        (Finset.union_nonempty.mpr (Or.inr hu))⟩
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1

theorem closedFaceStar_le (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    K.closedFaceStar s ≤ K := fun _ ht => ht.1

theorem closedFaceStar_antitone (K : SimplicialComplex 𝕜 E) : Antitone K.closedFaceStar := by
  intro s t hst r hr
  refine ⟨hr.1, K.down_closed hr.2 (Finset.union_subset_union hst Finset.Subset.rfl) ?_⟩
  exact Finset.union_nonempty.mpr (Or.inr (K.nonempty_of_mem_faces hr.1))

theorem finite_closedFaceStar_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) (s : Finset E) : (K.closedFaceStar s).faces.Finite :=
  hK.subset (K.closedFaceStar_le s)

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem starConvex_closedFaceStar (K : SimplicialComplex ℝ E) (s : Finset E)
    {p : E} (hp : p ∈ convexHull ℝ (s : Set E)) : StarConvex ℝ p (K.closedFaceStar s).space := by
  intro x hx a b ha hb hab
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
  have hst : s ∪ t ∈ (K.closedFaceStar s).faces :=
    ⟨ht.2, by simpa only [← Finset.union_assoc, Finset.union_self] using ht.2⟩
  apply convexHull_subset_space hst
  exact (convex_convexHull ℝ _)
    (convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_left) hp)
    (convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_right) hxt) ha hb hab

end Geometry.SimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isSecantTransverse_closedFaceStar_add_iff
    (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (P L : Submodule ℝ E)
    (hzero : (0 : E) ∈ convexHull ℝ (s : Set E))
    (hface : L.subtype ⁻¹' convexHull ℝ (s : Set E) ∈ 𝓝 (0 : L)) :
    P.IsSecantTransverse ((K.closedFaceStar s).space + (L : Set E)) ↔
      P.IsSecantTransverse (K.closedFaceStar s).space :=
  P.isSecantTransverse_add_submodule_iff L hzero
    (fun _ hp => K.starConvex_closedFaceStar s hp)
    (fun _ hl => Set.exists_pos_smul_mem_of_submodule_nhds L hface hl)

end Submodule

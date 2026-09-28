import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




def vertexSubcomplex (K : SimplicialComplex ℝ E) (V : Set E) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∀ v ∈ s, v ∈ V}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, fun v hv => hs.2 v (hts hv)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1



theorem vertexSubcomplex_le (K : SimplicialComplex ℝ E) (V : Set E) :
    K.vertexSubcomplex V ≤ K := fun _ hs => hs.1



theorem vertexSubcomplex_vertices (K : SimplicialComplex ℝ E) (V : Set E) :
    (K.vertexSubcomplex V).vertices = K.vertices ∩ V := by
  ext v
  change ({v} ∈ K.faces ∧ ∀ x ∈ ({v} : Finset E), x ∈ V) ↔
    ({v} ∈ K.faces ∧ v ∈ V)
  simp only [Finset.mem_singleton, forall_eq]



theorem vertexSubcomplex_finite (K : SimplicialComplex ℝ E) (V : Set E)
    (hK : K.faces.Finite) : (K.vertexSubcomplex V).faces.Finite :=
  hK.subset (K.vertexSubcomplex_le V)



theorem le_vertexSubcomplex {K L : SimplicialComplex ℝ E} {V : Set E}
    (hLK : L ≤ K) (hLV : L.vertices ⊆ V) : L ≤ K.vertexSubcomplex V := by
  intro s hs
  refine ⟨hLK hs, fun v hv => ?_⟩
  apply hLV
  exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

end Geometry.SimplicialComplex

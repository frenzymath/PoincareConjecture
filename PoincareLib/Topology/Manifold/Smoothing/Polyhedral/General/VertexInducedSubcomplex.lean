import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic

/-!
# Subcomplexes induced by a set of vertices

Retaining precisely the faces whose vertices lie in a given
set constructs the full induced subcomplex on those vertices.
This is used for the derived neighborhood retraction. See
Hudson 1969, pp. 8--9 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Retain exactly the original faces all of whose vertices
belong to the prescribed set. See Hudson pp. 8--9 and M76
derivation 270. -/
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

/-- A vertex-induced subcomplex is contained in its original
complex. See Hudson pp. 8--9 and M76 derivation 270. -/
theorem vertexSubcomplex_le (K : SimplicialComplex ℝ E) (V : Set E) :
    K.vertexSubcomplex V ≤ K := fun _ hs => hs.1

/-- The retained vertices are precisely the original vertices
in the prescribed set. See Hudson pp. 8--9 and derivation 270. -/
theorem vertexSubcomplex_vertices (K : SimplicialComplex ℝ E) (V : Set E) :
    (K.vertexSubcomplex V).vertices = K.vertices ∩ V := by
  ext v
  change ({v} ∈ K.faces ∧ ∀ x ∈ ({v} : Finset E), x ∈ V) ↔
    ({v} ∈ K.faces ∧ v ∈ V)
  simp only [Finset.mem_singleton, forall_eq]

/-- A vertex-induced subcomplex of a finite complex is finite.
See Hudson pp. 8--9 and M76 derivation 270. -/
theorem vertexSubcomplex_finite (K : SimplicialComplex ℝ E) (V : Set E)
    (hK : K.faces.Finite) : (K.vertexSubcomplex V).faces.Finite :=
  hK.subset (K.vertexSubcomplex_le V)

/-- A subcomplex whose vertices are all retained lies in the
vertex-induced subcomplex. See Hudson pp. 8--9 and derivation 270. -/
theorem le_vertexSubcomplex {K L : SimplicialComplex ℝ E} {V : Set E}
    (hLK : L ≤ K) (hLV : L.vertices ⊆ V) : L ≤ K.vertexSubcomplex V := by
  intro s hs
  refine ⟨hLK hs, fun v hv => ?_⟩
  apply hLV
  exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

end Geometry.SimplicialComplex

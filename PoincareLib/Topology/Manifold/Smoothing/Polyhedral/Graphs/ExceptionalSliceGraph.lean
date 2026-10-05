import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.StrictCrossingPointIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.GeometricGraphComponents

/-!
# The graph labels of an exceptional surface section

Adjoin the original zero vertex to the strict crossing-edge
labels. Triangular cofaces define all adjacencies. Realization
is injective and retains the possible isolated exceptional point.
See Alexander 1924, pp. 6--8 and M76 derivation 147.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Original edges strictly crossing the affine zero plane.
This definition permits zero vertices elsewhere in the complex.
See Alexander p. 6 and M76 derivation 147. -/
def strictCrossingEdges (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) : Set (Finset E) :=
  {e | e ∈ K.faces ∧ A.StraddlesZero e}

/-- A finite original complex has finitely many strict crossing
labels at every level. See Alexander p. 6 and derivation 147. -/
theorem finite_strictCrossingEdges (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hK : K.faces.Finite) : (K.strictCrossingEdges A).Finite :=
  hK.subset (fun _ he => he.1)

/-- The exceptional label realizes to the original vertex;
every other label realizes to its edge crossing. See Alexander
pp. 6--8 and M76 derivation 147. -/
noncomputable def exceptionalCrossingPoint (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (q : E) : Option (K.strictCrossingEdges A) → E
  | none => q
  | some e => A.straddlingPoint e.val e.property.2

/-- Original triangular cofaces define the exceptional section
graph. A triangle through the exceptional vertex joins that
vertex to its strictly crossing opposite edge.
See Alexander pp. 6--8 and M76 derivation 147. -/
def exceptionalSliceGraph [DecidableEq E]
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (q : E) :
    SimpleGraph (Option (K.strictCrossingEdges A)) where
  Adj a b := match a, b with
    | none, none => False
    | none, some e => insert q e.val ∈ K.faces ∧ (insert q e.val).card = 3
    | some e, none => insert q e.val ∈ K.faces ∧ (insert q e.val).card = 3
    | some e, some f => e ≠ f ∧ ∃ t ∈ K.faces, t.card = 3 ∧ e.val ⊆ t ∧ f.val ⊆ t
  symm := ⟨by
    intro a b h
    cases a with
    | none => cases b <;> exact h
    | some e =>
      cases b with
      | none => exact h
      | some f =>
        obtain ⟨hne, t, ht, hc, he, hf⟩ := h
        exact ⟨hne.symm, t, ht, hc, hf, he⟩⟩
  loopless := ⟨by
    intro a h
    cases a with
    | none => exact h
    | some e => exact h.1 rfl⟩

/-- An original exceptional vertex and all strict crossing
edges have distinct realization points. See Alexander pp. 6--8
and M76 derivation 147. -/
theorem exceptionalCrossingPoint_injective (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ K.vertices) :
    Function.Injective (K.exceptionalCrossingPoint A q) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some f =>
      exact False.elim (K.straddlingPoint_ne_vertex A f.property.1 f.property.2 hq hab.symm)
  | some e =>
    cases b with
    | none =>
      exact False.elim (K.straddlingPoint_ne_vertex A e.property.1 e.property.2 hq hab)
    | some f =>
      exact congrArg some (K.straddlingPoint_injective_without_regularity A hab)

/-- Every exceptional graph vertex lies in the actual surface
section when the distinguished vertex is an original zero vertex.
See Alexander p. 6 and M76 derivation 147. -/
theorem exceptionalCrossingPoint_mem (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ K.vertices) (hAq : A q = 0)
    (v : Option (K.strictCrossingEdges A)) :
    K.exceptionalCrossingPoint A q v ∈ K.space ∩ {x | A x = 0} := by
  cases v with
  | none => exact ⟨K.vertices_subset_space hq, hAq⟩
  | some e =>
    have he := A.straddlingPoint_mem e.val e.property.2
    exact ⟨K.convexHull_subset_space e.property.1 he.1, he.2⟩

end Geometry.SimplicialComplex

import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.LocalHeights.Compatibility

/-!
# Original crossing-edge labels for triangle-local heights

A crossing is labeled by its original source edge. Choose an actual
incident triangle only to evaluate its point; compatible local zero sets
make that point independent of the chosen triangle.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Actual source edges crossing the zero set in an incident triangle. -/
def triangleCrossingEdges (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Set (Finset E) :=
  {e | e ∈ K.faces ∧ ∃ t ∈ K.faces, t.card = 3 ∧ e ⊆ t ∧ (A t).StraddlesZero e}

/-- A chosen actual incident triangle of the original crossing edge. -/
noncomputable def triangleCrossingTriangle (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) : Finset E :=
  e.property.2.choose

theorem triangleCrossingTriangle_spec (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) :
    K.triangleCrossingTriangle A e ∈ K.faces ∧
      (K.triangleCrossingTriangle A e).card = 3 ∧
      e.val ⊆ K.triangleCrossingTriangle A e ∧
      (A (K.triangleCrossingTriangle A e)).StraddlesZero e.val :=
  e.property.2.choose_spec

/-- Each original crossing label is a genuine two-vertex edge. -/
theorem triangleCrossingEdge_card (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) : e.val.card = 2 :=
  (K.triangleCrossingTriangle_spec A e).2.2.2.card

/-- Evaluate the original-edge crossing in its chosen local triangle. -/
noncomputable def triangleCrossingPoint (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) : E :=
  (A (K.triangleCrossingTriangle A e)).straddlingPoint e.val
    (K.triangleCrossingTriangle_spec A e).2.2.2

theorem triangleCrossingPoint_mem (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) :
    K.triangleCrossingPoint A e ∈ convexHull ℝ (e.val : Set E) ∧
      A (K.triangleCrossingTriangle A e) (K.triangleCrossingPoint A e) = 0 :=
  (A (K.triangleCrossingTriangle A e)).straddlingPoint_mem e.val
    (K.triangleCrossingTriangle_spec A e).2.2.2

/-- Every incident triangle sees the same strict original-edge crossing. -/
theorem triangleCrossingEdge_straddles (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (e : K.triangleCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (het : e.val ⊆ t) :
    (A t).StraddlesZero e.val := by
  have hs := K.triangleCrossingTriangle_spec A e
  exact (hA.straddlesZero_iff hs.1 hs.2.1 ht htc hs.2.2.1 het).mp hs.2.2.2

/-- Evaluation in any actual incident chart gives the chosen crossing point. -/
theorem triangleCrossingPoint_eq (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (e : K.triangleCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (het : e.val ⊆ t)
    (he : (A t).StraddlesZero e.val) :
    K.triangleCrossingPoint A e = (A t).straddlingPoint e.val he := by
  have hs := K.triangleCrossingTriangle_spec A e
  exact hA.straddlingPoint_eq hs.1 hs.2.1 ht htc hs.2.2.1 het hs.2.2.2 he

/-- Original-edge geometry distinguishes crossing points even before
compatibility of the local heights is used. -/
theorem triangleCrossingPoint_injective (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Function.Injective (K.triangleCrossingPoint A) := by
  intro e f h
  have he := K.triangleCrossingPoint_mem A e
  have hf := K.triangleCrossingPoint_mem A f
  apply Subtype.ext
  exact K.eq_edge_of_straddling_zero_point (A (K.triangleCrossingTriangle A e))
    e.property.1 f.property.1 (K.triangleCrossingTriangle_spec A e).2.2.2
    (K.triangleCrossingEdge_card A f) he.1 (h ▸ hf.1) he.2

/-- No actual crossing point is an original source vertex. -/
theorem triangleCrossingPoint_ne_vertex (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A)
    {q : E} (hq : q ∈ K.vertices) : K.triangleCrossingPoint A e ≠ q :=
  K.straddlingPoint_ne_vertex (A (K.triangleCrossingTriangle A e)) e.property.1
    (K.triangleCrossingTriangle_spec A e).2.2.2 hq

/-- Finite original complexes have only finitely many crossing labels. -/
theorem finite_triangleCrossingEdges (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) :
    (K.triangleCrossingEdges A).Finite := hK.subset (fun _ he => he.1)

end Geometry.SimplicialComplex

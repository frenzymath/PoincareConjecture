import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Compatibility









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]


def triangleCrossingEdges (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Set (Finset E) :=
  {e | e ∈ K.faces ∧ ∃ t ∈ K.faces, t.card = 3 ∧ e ⊆ t ∧ (A t).StraddlesZero e}


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


theorem triangleCrossingEdge_card (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A) : e.val.card = 2 :=
  (K.triangleCrossingTriangle_spec A e).2.2.2.card


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


theorem triangleCrossingEdge_straddles (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (e : K.triangleCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (het : e.val ⊆ t) :
    (A t).StraddlesZero e.val := by
  have hs := K.triangleCrossingTriangle_spec A e
  exact (hA.straddlesZero_iff hs.1 hs.2.1 ht htc hs.2.2.1 het).mp hs.2.2.2


theorem triangleCrossingPoint_eq (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (e : K.triangleCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (het : e.val ⊆ t)
    (he : (A t).StraddlesZero e.val) :
    K.triangleCrossingPoint A e = (A t).straddlingPoint e.val he := by
  have hs := K.triangleCrossingTriangle_spec A e
  exact hA.straddlingPoint_eq hs.1 hs.2.1 ht htc hs.2.2.1 het hs.2.2.2 he



theorem triangleCrossingPoint_injective (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Function.Injective (K.triangleCrossingPoint A) := by
  intro e f h
  have he := K.triangleCrossingPoint_mem A e
  have hf := K.triangleCrossingPoint_mem A f
  apply Subtype.ext
  exact K.eq_edge_of_straddling_zero_point (A (K.triangleCrossingTriangle A e))
    e.property.1 f.property.1 (K.triangleCrossingTriangle_spec A e).2.2.2
    (K.triangleCrossingEdge_card A f) he.1 (h ▸ hf.1) he.2


theorem triangleCrossingPoint_ne_vertex (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (e : K.triangleCrossingEdges A)
    {q : E} (hq : q ∈ K.vertices) : K.triangleCrossingPoint A e ≠ q :=
  K.straddlingPoint_ne_vertex (A (K.triangleCrossingTriangle A e)) e.property.1
    (K.triangleCrossingTriangle_spec A e).2.2.2 hq


theorem finite_triangleCrossingEdges (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) :
    (K.triangleCrossingEdges A).Finite := hK.subset (fun _ he => he.1)

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.CrossingLabels
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def triangleZeroSet (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | ∃ t ∈ K.faces, t.card = 3 ∧ x ∈ convexHull ℝ (t : Set E) ∧ A t x = 0}

def triangleZeroVertices (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Set E :=
  {q | q ∈ K.vertices ∧ ∃ t ∈ K.faces, t.card = 3 ∧ q ∈ t ∧ A t q = 0}

theorem triangleZeroVertex_zero (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (q : K.triangleZeroVertices A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (hqt : q.val ∈ t) : A t q.val = 0 := by
  obtain ⟨s, hs, hsc, hqs, hzero⟩ := q.property.2
  exact (hA s hs hsc t ht htc q.val (subset_convexHull ℝ (s : Set E) hqs)
    (subset_convexHull ℝ (t : Set E) hqt)).mp hzero

abbrev TriangleSliceLabel (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) :=
  K.triangleZeroVertices A ⊕ K.triangleCrossingEdges A

noncomputable def triangleSlicePoint (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : K.TriangleSliceLabel A → E
  | .inl q => q.val
  | .inr e => K.triangleCrossingPoint A e

theorem triangleSlicePoint_injective (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Function.Injective (K.triangleSlicePoint A) := by
  intro a b h
  cases a with
  | inl q =>
    cases b with
    | inl r => exact congrArg Sum.inl (Subtype.ext h)
    | inr e => exact False.elim (K.triangleCrossingPoint_ne_vertex A e q.property.1 h.symm)
  | inr e =>
    cases b with
    | inl q => exact False.elim (K.triangleCrossingPoint_ne_vertex A e q.property.1 h)
    | inr f => exact congrArg Sum.inr (K.triangleCrossingPoint_injective A h)

theorem triangleSlicePoint_mem (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (v : K.TriangleSliceLabel A) :
    K.triangleSlicePoint A v ∈ K.triangleZeroSet A := by
  cases v with
  | inl q =>
    obtain ⟨t, ht, htc, hqt, hz⟩ := q.property.2
    exact ⟨t, ht, htc, subset_convexHull ℝ (t : Set E) hqt, hz⟩
  | inr e =>
    have ht := K.triangleCrossingTriangle_spec A e
    have hp := K.triangleCrossingPoint_mem A e
    exact ⟨K.triangleCrossingTriangle A e, ht.1, ht.2.1,
      convexHull_mono ht.2.2.1 hp.1, hp.2⟩

variable [DecidableEq E]

def triangleSliceOriginalVertices (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : K.TriangleSliceLabel A → Finset E
  | .inl q => {q.val}
  | .inr e => e.val

def triangleSliceGraph (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : SimpleGraph (K.TriangleSliceLabel A) where
  Adj a b :=
    K.triangleSliceOriginalVertices A a ∪ K.triangleSliceOriginalVertices A b ∈ K.faces ∧
      (K.triangleSliceOriginalVertices A a ∪ K.triangleSliceOriginalVertices A b).card = 3
  symm := ⟨by intro a b h; simpa only [Finset.union_comm] using h⟩
  loopless := ⟨by
    intro a h
    rw [Finset.union_self] at h
    cases a with
    | inl q => simpa [triangleSliceOriginalVertices] using h.2
    | inr e =>
      have hc3 : e.val.card = 3 := h.2
      have hc := K.triangleCrossingEdge_card A e
      omega⟩

theorem triangleSliceGraph_not_adj_zero (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) (q r : K.triangleZeroVertices A) :
    ¬ (K.triangleSliceGraph A).Adj (.inl q) (.inl r) := by
  intro h
  have hc : ({q.val, r.val} : Finset E).card = 3 := by
    simpa [triangleSliceGraph, triangleSliceOriginalVertices] using h.2
  by_cases hqr : q.val = r.val <;> simp [hqr] at hc

end Geometry.SimplicialComplex

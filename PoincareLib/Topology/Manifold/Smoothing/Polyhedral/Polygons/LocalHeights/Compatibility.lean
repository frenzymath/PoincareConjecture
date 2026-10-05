import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.LocalHeights.SharedEdgeCrossing

/-!
# Compatible zero sets of actual triangle heights

Only zero sets must agree on common source points. A common mapped
frontier supplies this compatibility directly, even when chart heights
have different magnitudes or opposite sign conventions.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The triangle-local heights define the same zero set on every overlap. -/
def CompatibleTriangleZeroSets (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s ∈ K.faces, s.card = 3 → ∀ t ∈ K.faces, t.card = 3 →
    ∀ x ∈ convexHull ℝ (s : Set E), x ∈ convexHull ℝ (t : Set E) →
      (A s x = 0 ↔ A t x = 0)

/-- Actual local defining equations for the same mapped frontier give
zero-set compatibility; no common scalar function is required. -/
theorem compatibleTriangleZeroSets_of_common_preimage (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) {F : Type*} (f : E → F) (N : Set F)
    (h : ∀ t ∈ K.faces, t.card = 3 → ∀ x ∈ convexHull ℝ (t : Set E),
      A t x = 0 ↔ f x ∈ N) : K.CompatibleTriangleZeroSets A := by
  intro s hs hsc t ht htc x hxs hxt
  exact (h s hs hsc x hxs).trans (h t ht htc x hxt).symm

/-- Compatibility on triangles restricts to any actual common edge. -/
theorem CompatibleTriangleZeroSets.on_edge {K : SimplicialComplex ℝ E}
    {A : Finset E → E →ᵃ[ℝ] ℝ} (h : K.CompatibleTriangleZeroSets A)
    {s t e : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (ht : t ∈ K.faces) (htc : t.card = 3) (hes : e ⊆ s) (het : e ⊆ t) :
    ∀ x ∈ convexHull ℝ (e : Set E), A s x = 0 ↔ A t x = 0 := by
  intro x hx
  exact h s hs hsc t ht htc x (convexHull_mono hes hx) (convexHull_mono het hx)

/-- Strict crossing is independent of the incident triangle's chart. -/
theorem CompatibleTriangleZeroSets.straddlesZero_iff {K : SimplicialComplex ℝ E}
    {A : Finset E → E →ᵃ[ℝ] ℝ} (h : K.CompatibleTriangleZeroSets A)
    {s t e : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (ht : t ∈ K.faces) (htc : t.card = 3) (hes : e ⊆ s) (het : e ⊆ t) :
    (A s).StraddlesZero e ↔ (A t).StraddlesZero e :=
  ⟨fun he => he.of_zero_set_eq (h.on_edge hs hsc ht htc hes het),
    fun he => he.of_zero_set_eq (h.on_edge ht htc hs hsc het hes)⟩

/-- The original-edge crossing point is independent of the local chart. -/
theorem CompatibleTriangleZeroSets.straddlingPoint_eq {K : SimplicialComplex ℝ E}
    {A : Finset E → E →ᵃ[ℝ] ℝ} (h : K.CompatibleTriangleZeroSets A)
    {s t e : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (ht : t ∈ K.faces) (htc : t.card = 3) (hes : e ⊆ s) (het : e ⊆ t)
    (he : (A s).StraddlesZero e) (he' : (A t).StraddlesZero e) :
    (A s).straddlingPoint e he = (A t).straddlingPoint e he' :=
  AffineMap.straddlingPoint_eq_of_zero_set_eq he he' (h.on_edge hs hsc ht htc hes het)

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y] [T1Space Y]

theorem finite_label_eq_on_face (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) {D : Set Y} (hD : D.Finite)
    (hf : MapsTo f K.space D) {s : Finset E} (hs : s ∈ K.faces)
    {x y : E} (hx : x ∈ convexHull ℝ (s : Set E))
    (hy : y ∈ convexHull ℝ (s : Set E)) : f x = f y := by
  exact (convex_convexHull ℝ (s : Set E)).isPreconnected.constant_of_mapsTo
    hD.isDiscrete (hc.mono (K.convexHull_subset_space hs))
    (fun _ hz => hf (K.convexHull_subset_space hs hz)) hx hy

theorem vertexSubcomplex_space_eq_finite_label (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) {D : Set Y} (hD : D.Finite)
    (hf : MapsTo f K.space D) (a : Y) :
    (K.vertexSubcomplex {x | f x = a}).space = K.space ∩ f ⁻¹' {a} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (K.vertexSubcomplex {x | f x = a}).mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
    refine ⟨K.convexHull_subset_space hs.1 hxs, ?_⟩
    exact (K.finite_label_eq_on_face hc hD hf hs.1 hxs
      (subset_convexHull ℝ _ hv)).trans (hs.2 v hv)
  · rintro ⟨hx, hxa⟩
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    apply (K.vertexSubcomplex {x | f x = a}).mem_space_iff.mpr
    refine ⟨s, ⟨hs, ?_⟩, hxs⟩
    intro v hv
    exact (K.finite_label_eq_on_face hc hD hf hs
      (subset_convexHull ℝ _ hv) hxs).trans hxa

theorem two_label_subcomplex_cover (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) (a b : Y)
    (hf : MapsTo f K.space ({a, b} : Set Y)) :
    K.space = (K.vertexSubcomplex {x | f x = a}).space ∪
      (K.vertexSubcomplex {x | f x = b}).space := by
  rw [K.vertexSubcomplex_space_eq_finite_label hc ((finite_singleton b).insert a) hf a,
    K.vertexSubcomplex_space_eq_finite_label hc ((finite_singleton b).insert a) hf b]
  ext x
  constructor
  · intro hx
    rcases hf hx with ha | hb
    · exact Or.inl ⟨hx, ha⟩
    · exact Or.inr ⟨hx, hb⟩
  · rintro (hx | hx)
    · exact hx.1
    · exact hx.1

theorem finite_label_subcomplex_disjoint (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) {D : Set Y} (hD : D.Finite)
    (hf : MapsTo f K.space D) {a b : Y} (hab : a ≠ b) :
    Disjoint (K.vertexSubcomplex {x | f x = a}).space
      (K.vertexSubcomplex {x | f x = b}).space := by
  rw [K.vertexSubcomplex_space_eq_finite_label hc hD hf a,
    K.vertexSubcomplex_space_eq_finite_label hc hD hf b]
  apply disjoint_left.mpr
  intro x hx hy
  exact hab (hx.2.symm.trans hy.2)

theorem isClopen_finite_label_level (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) {D : Set Y} (hD : D.Finite)
    (hf : MapsTo f K.space D) (a : Y) :
    IsClopen {x : K.space | f x = a} := by
  have hcrestrict : Continuous (fun x : K.space => f x) :=
    continuousOn_iff_continuous_domRestrict.mp hc
  refine ⟨isClosed_singleton.preimage hcrestrict, ?_⟩
  have hother : IsClosed (D \ {a}) := (hD.subset sdiff_subset).isClosed
  have hlevel : {x : K.space | f x = a} =
      ((fun x : K.space => f x) ⁻¹' (D \ {a}))ᶜ := by
    ext x
    constructor
    · intro hx hnot
      exact hnot.2 hx
    · intro hx
      by_contra hne
      exact hx ⟨hf x.property, hne⟩
  rw [hlevel]
  exact (hother.preimage hcrestrict).isOpen_compl

theorem affineOnFaces_finite_label (K : SimplicialComplex ℝ E)
    {f : E → Y} (hc : ContinuousOn f K.space) {D : Set Y} (hD : D.Finite)
    (hf : MapsTo f K.space D) (w : Y → ℝ) :
    K.AffineOnFaces (fun x => w (f x)) := by
  intro s hs
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  refine ⟨ContinuousAffineMap.const ℝ E (w (f v)), ?_⟩
  intro x hx
  exact congrArg w (K.finite_label_eq_on_face hc hD hf hs hx
    (subset_convexHull ℝ _ hv))

theorem finitePiecewiseAffineOn_finite_label (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {f : E → Y} (hc : ContinuousOn f K.space)
    {D : Set Y} (hD : D.Finite) (hf : MapsTo f K.space D) (w : Y → ℝ) :
    FinitePiecewiseAffineOn (fun x => w (f x)) K.space :=
  (K.affineOnFaces_finite_label hc hD hf w).finitePiecewiseAffineOn hK

end Geometry.SimplicialComplex

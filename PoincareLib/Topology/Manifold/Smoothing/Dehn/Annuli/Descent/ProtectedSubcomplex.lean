import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.ProtectedBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralRefinement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralIntersections
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedraSubcomplexes

/-!
# A constructed full protected subcomplex around all source rims

The collision-free neighborhood contains a finite polyhedral neighborhood
of the complete boundary. Intersect it with the actual source and refine
once to obtain a full subcomplex. Its whole carrier has singleton fibers
against the entire original source, not merely against the protected part.
-/

set_option autoImplicit false

open Set Geometry Topology Metric
open PoincareMT.M76.Dehn

namespace Geometry.SimplicialComplex

/-- A compact part of a finite source has a full subcomplex neighborhood
inside any prescribed ambient open neighborhood, after actual subdivision. -/
theorem exists_full_relative_neighborhood
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {Q W : Set V} (hQ : IsCompact Q) (hQK : Q ⊆ K.space)
    (hW : IsOpen W) (hQW : Q ⊆ W) :
    ∃ P K' A : SimplicialComplex ℝ V,
      P.faces.Finite ∧ K'.faces.Finite ∧ K'.IsSubdivision K ∧ A ≤ K' ∧
      A.space = K.space ∩ P.space ∧ Q ⊆ interior P.space ∧ P.space ⊆ W ∧
      Q ⊆ A.space ∧
      ∀ a ∈ K'.faces, (∀ v ∈ a, v ∈ A.vertices) → a ∈ A.faces := by
  obtain ⟨P, hP, hQP, hPW⟩ := exists_finite_neighborhood_subset_normed hQ hW hQW
  obtain ⟨A₀, hA₀, hA₀s⟩ := K.exists_finite_triangulation_inter P hK hP
  obtain ⟨K', A, hK', hK'K, hA⟩ := K.exists_subdivision_with_finite_full_polyhedra hK
    (fun _ : Unit ↦ A₀) (fun _ ↦ hA₀) (fun _ ↦ hA₀s.subset.trans inter_subset_left)
  have hAs : (A ()).space = K.space ∩ P.space := (hA ()).2.1.trans hA₀s
  exact ⟨P, K', A (), hP, hK', hK'K, (hA ()).1, hAs, hQP, hPW,
    fun x hx ↦ hAs.symm.subset ⟨hQK hx, interior_subset (hQP hx)⟩, (hA ()).2.2⟩

end Geometry.SimplicialComplex

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}

/-- Original upper embedding, whole-frontier properness, and the prescribed
boundary injection construct the full protected source mark for descent. -/
theorem Step.exists_protected_source_subcomplex (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space ↦ j x))
    (Q : Set V) (hQ : IsCompact Q) (hQK : Q ⊆ K.space) (R : Set M)
    (hproper : ∀ x ∈ K.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Q)
    (hrim : InjOn (t.projection ∘ j) Q) :
    let p := (step.projection ∘ step.inclusion) ∘ j
    ∃ P K' A : SimplicialComplex ℝ V,
      P.faces.Finite ∧ K'.faces.Finite ∧ K'.IsSubdivision K ∧ A ≤ K' ∧
      A.space = K.space ∩ P.space ∧ Q ⊆ interior P.space ∧ Q ⊆ A.space ∧
      (∀ a ∈ K'.faces, (∀ v ∈ a, v ∈ A.vertices) → a ∈ A.faces) ∧
      Disjoint A.space (doubleLocusOn p K.space) ∧
      (∀ x ∈ A.space, ∀ y ∈ K.space, p x = p y → x = y) := by
  dsimp only
  obtain ⟨D, _, _, _, hDs, hDc, _, hDQ, _⟩ :=
    step.exists_protected_boundary_projection K hK hj hji Q hQ hQK R hproper hrim
  obtain ⟨P, K', A, hP, hK', hK'K, hAK', hAs, hQP, hPD, hQA, hfull⟩ :=
    K.exists_full_relative_neighborhood hK hQ hQK hDc.isClosed.isOpen_compl
      (fun _ hx hxD ↦ disjoint_left.mp hDQ hxD hx)
  refine ⟨P, K', A, hP, hK', hK'K, hAK', hAs, hQP, hQA, hfull, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ hx hxd ↦ hPD (hAs.subset hx).2 (hDs.symm.subset hxd)
  · intro x hx y hy hxy
    by_contra hne
    exact hPD (hAs.subset hx).2
      (hDs.symm.subset ⟨(hAs.subset hx).1, y, hy, hxy, hne⟩)

end Geometry.OriginalPLTower

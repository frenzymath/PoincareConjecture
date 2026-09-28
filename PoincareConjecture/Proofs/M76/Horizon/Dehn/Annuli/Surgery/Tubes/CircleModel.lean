import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.ComponentBranchModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.PhysicalPolygon
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {S : Set E} {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceCircleDecomposition f S} {i : old.Index}



theorem ComponentBranchModel.exists_axis_order
    (D : ComponentBranchModel (e := e) (R := R) old i) :
    ∃ (m : ℕ) (p : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective p ∧
      p.HasSimplicialEdges ∧ range p = D.axis.vertices ∧ p.boundary ℝ = D.axis.space ∧
      (∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔ s.Nonempty ∧
        ∃ j : Fin (m + 3), s ⊆ {p j, p (finRotate (m + 3) j)}) ∧
      ∀ s : Finset (D.sample → ℝ × V3), (s ∈ D.axis.faces ∧ s.card = 2) ↔
        ∃ j : Fin (m + 3), s = {p j, p (finRotate (m + 3) j)} := by
  classical
  have hfaithful : InjOn D.graph (f '' old.pieces i) := by
    intro x hx y _ hxy
    exact D.graph_separates x (interior_subset (D.core_neighborhood hx)) y hxy
  obtain ⟨n, P, hPi, hP, hPs⟩ := old.exists_physical_polygon i D.graph D.selected_PL hfaithful
  have hconn : IsConnected D.axis.space := by
    rw [D.axis_space]
    exact (old.pieces_isConnected i).image (D.graph ∘ f) D.selected_PL.continuousOn
  exact D.axis.exists_exact_cyclic_polygon_of_polygon_carrier
    (D.complex_finite.subset D.axis_le) hconn P hP hPi (hPs.trans D.axis_space.symm)



theorem SourceCircleDecomposition.exists_interior_circle_model [T2Space X]
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite) (hQS : Q.space = S)
    (old : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (hinterior : MapsTo f (doubleLocusOn f S) (interior R))
    (i : old.Index) :
    ∃ D : ComponentBranchModel (e := e) (R := R) old i,
      D.core ⊆ interior R ∧ (∀ y, (D.charts y).source ⊆ interior R) ∧
      ∃ (m : ℕ) (p : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective p ∧
        p.HasSimplicialEdges ∧ range p = D.axis.vertices ∧ p.boundary ℝ = D.axis.space ∧
        (∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔ s.Nonempty ∧
          ∃ j : Fin (m + 3), s ⊆ {p j, p (finRotate (m + 3) j)}) ∧
        ∀ s : Finset (D.sample → ℝ × V3), (s ∈ D.axis.faces ∧ s.card = 2) ↔
          ∃ j : Fin (m + 3), s = {p j, p (finRotate (m + 3) j)} := by
  have hinside : f '' old.pieces i ⊆ interior R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hinterior (old.piece_subset_double i hx)
  obtain ⟨D, hD, hcharts⟩ := old.exists_component_branch_model Q hQ hQS hf he hcross i
    isOpen_interior hinside
  exact ⟨D, hD, hcharts, D.exists_axis_order⟩

end PoincareConjecture.M76.Dehn.Annuli


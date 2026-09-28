import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentBranchModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SelfPairedPhysicalPolygon
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem ComponentBranchModel.exists_selfpaired_axis_order
    (D : ComponentBranchModel old i)
    (hf : PolyhedralPLInCharts e f D2) (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) (hself : old.mate i = i) :
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
  obtain ⟨n, P, hPi, hP, hPs⟩ := old.exists_selfpaired_physical_polygon
    hf hin hfront i hself D.graph D.selected_PL hfaithful
  have hconn : IsConnected D.axis.space := by
    rw [D.axis_space]
    exact (old.connected i).image (D.graph ∘ f) D.selected_PL.continuousOn
  exact D.axis.exists_exact_cyclic_polygon_of_polygon_carrier
    (D.complex_finite.subset D.axis_le) hconn P hP hPi (hPs.trans D.axis_space.symm)

theorem OrdinaryDoubleCurveModel.exists_selfpaired_circle_model
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R) (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : old.Index) (hself : old.mate i = i) (hiQ : Disjoint (old.pieces i) Q2) :
    ∃ D : ComponentBranchModel old i, D.core ⊆ interior R ∧
      (∀ y, (D.charts y).source ⊆ interior R) ∧
      ∃ (m : ℕ) (p : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective p ∧
        p.HasSimplicialEdges ∧ range p = D.axis.vertices ∧ p.boundary ℝ = D.axis.space ∧
        (∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔ s.Nonempty ∧
          ∃ j : Fin (m + 3), s ⊆ {p j, p (finRotate (m + 3) j)}) ∧
        ∀ s : Finset (D.sample → ℝ × V3), (s ∈ D.axis.faces ∧ s.card = 2) ↔
          ∃ j : Fin (m + 3), s = {p j, p (finRotate (m + 3) j)} := by
  have hinside : f '' old.pieces i ⊆ interior R := by
    rintro y ⟨x, hx, rfl⟩
    have hxD := (old.piece_subset_double i hx).1
    rw [← self_sdiff_frontier]
    exact ⟨hin hxD, fun h ↦ disjoint_left.mp hiQ hx ((hfront x hxD).mp h)⟩
  obtain ⟨D, hD, hcharts⟩ :=
    old.exists_component_branch_model hf he i isOpen_interior hinside
  exact ⟨D, hD, hcharts, D.exists_selfpaired_axis_order hf hin hfront hself⟩

end PoincareConjecture.M76.Dehn

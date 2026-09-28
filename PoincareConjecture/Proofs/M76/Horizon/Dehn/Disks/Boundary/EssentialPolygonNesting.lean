import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected










set_option autoImplicit false
open Set Metric Topology

namespace PoincareConjecture.M76.Dehn

open PoincareConjecture Poincare.Manifold.Schoenflies

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Plane" => (ℝ × ℝ)



theorem squareRimLoop_class_eq_one_of_polygon_disk
    {n : ℕ} (P : Polygon Plane (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {U : Set Plane} (hPU : closure P.inside ⊆ U)
    (gamma : C(Q2, U)) (hgamma : ∀ x, (gamma x : Plane) ∈ closure P.inside) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) = 1 := by
  obtain ⟨e, _⟩ := P.exists_closed_inside_homeomorph_closedBall hP hinj
  let : ContractibleSpace (closedBall (0 : Plane) 1) :=
    (convex_closedBall (0 : Plane) 1).contractibleSpace
      ⟨0, mem_closedBall_self (by norm_num)⟩
  let : ContractibleSpace (closure P.inside) := e.contractibleSpace
  let lifted : C(Q2, closure P.inside) :=
    ⟨fun x ↦ ⟨gamma x, hgamma x⟩,
      (continuous_subtype_val.comp gamma.continuous).subtype_mk _⟩
  let inclusion : C(closure P.inside, U) :=
    ⟨fun x ↦ ⟨x, hPU x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hnull := (SimplyConnectedSpace.paths_homotopic
    (squareRimLoop.map lifted.continuous) (Path.refl (lifted squareRimBase))).map inclusion
  exact Path.Homotopic.Quotient.eq.mpr hnull



theorem essential_polygon_encloses_inner_disk
    {m n k : ℕ} (outer : Polygon Plane (m + 3))
    (inner : Polygon Plane (n + 3)) (rim : Polygon Plane (k + 3))
    (ho : outer.HasSimplicialEdges) (hio : Function.Injective outer)
    (hi : inner.HasSimplicialEdges) (hii : Function.Injective inner)
    (hr : rim.HasSimplicialEdges) (hir : Function.Injective rim)
    (hboundary : rim.boundary ℝ ⊆ outer.inside \ closure inner.inside)
    (gamma : C(Q2, {x : Plane // x ∈ outer.inside \ closure inner.inside}))
    (hgamma : ∀ x, (gamma x : Plane) ∈ rim.boundary ℝ)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    closure inner.inside ⊆ rim.inside := by
  have hbinner : inner.boundary ℝ ⊆ closure inner.inside := by
    rw [← inner.frontier_inside hi hii]
    exact frontier_subset_closure
  have hbrim : rim.boundary ℝ ⊆ closure rim.inside := by
    rw [← rim.frontier_inside hr hir]
    exact frontier_subset_closure
  have hdisj : Disjoint (inner.boundary ℝ) (rim.boundary ℝ) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ (hboundary hy).2 (hbinner hx)
  rcases inner.closed_inside_nested_or_disjoint rim hi hii hr hir hdisj with
      hnest | hnest | hsep
  · exact hnest
  · obtain ⟨x, hx⟩ := (rim.isConnected_boundary hr hir).nonempty
    exact ((hboundary hx).2 (subset_closure (hnest (hbrim hx)))).elim
  · have houter : closure rim.inside ⊆ outer.inside :=
      outer.closure_inside_subset_inside_of_boundary_subset_inside rim ho hio hr hir
        (fun _ hx ↦ (hboundary hx).1)
    have hcontained : closure rim.inside ⊆ outer.inside \ closure inner.inside :=
      fun x hx ↦ ⟨houter hx, fun hy ↦ Set.disjoint_left.mp hsep hy hx⟩
    exact (hessential (squareRimLoop_class_eq_one_of_polygon_disk rim hr hir hcontained
      gamma (fun x ↦ hbrim (hgamma x)))).elim

end PoincareConjecture.M76.Dehn

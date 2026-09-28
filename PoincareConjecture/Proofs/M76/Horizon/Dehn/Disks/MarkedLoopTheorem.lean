import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.ContinuousTerminalMarkedDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.OriginalMarkedProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.StageDescent

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem nonempty_marked_boundary_PL_loop_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (hR : PLDomain e R)
    (F : Set X) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (f : C(D2, R)) (gamma : C(Q2, F))
    (hgamma : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X))
    (J : Subgroup (FundamentalGroup F (gamma squareRimBase))) (hJ : J.Normal)
    (houtside : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ∉ J) :
    Nonempty (MarkedBoundaryPLLoopDisk e R F (gamma squareRimBase) J) := by
  let := hJ
  obtain ⟨g, S, r, C, s0, st, _hS, hs0, hreach, ⟨terminal⟩⟩ :=
    OriginalPLTower.exists_continuous_terminal_marked_disk hR hF hFopen f gamma hgamma J houtside
  obtain ⟨folded⟩ := OriginalPLTower.nonempty_folded_stage_marked_disk hR hF hFopen hreach terminal
  exact ⟨folded.project hs0⟩

theorem exists_marked_boundary_PL_loop_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (hR : PLDomain e R)
    (F : Set X) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (f : C(D2, R)) (gamma : C(Q2, F))
    (hgamma : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X))
    (J : Subgroup (FundamentalGroup F (gamma squareRimBase))) (hJ : J.Normal)
    (houtside : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ∉ J) :
    ∃ (j : V2 → X) (gammaOut : C(Q2, F)),
      PolyhedralPLInCharts e j D2 ∧ IsEmbedding (fun x : D2 ↦ j x) ∧ MapsTo j D2 R ∧
      (∀ x : Q2, j x = (gammaOut x : X)) ∧
      (∀ x : D2, j x ∈ frontier R ↔ (x : V2) ∈ Q2) ∧
      ∃ p : Path (gamma squareRimBase) (gammaOut squareRimBase),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((p.trans (squareRimLoop.map gammaOut.continuous)).trans p.symm)) ∉ J := by
  obtain ⟨disk⟩ := nonempty_marked_boundary_PL_loop_disk e R hR F hF hFopen
    f gamma hgamma J hJ houtside
  exact ⟨disk.map, disk.rim, disk.piecewiseAffine, disk.embedding, disk.inside,
    disk.boundary_values, disk.whole_boundary_iff, disk.basepath, disk.outside⟩

end PoincareConjecture.M76.Dehn

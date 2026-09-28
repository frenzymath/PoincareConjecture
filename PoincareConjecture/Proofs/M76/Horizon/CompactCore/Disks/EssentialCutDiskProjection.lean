import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedDiskCutSide
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.LoopClassTransport
import PoincareConjecture.Proofs.M76.Dehn.MarkedBoundaryPLLoopDisk

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem Dehn.MarkedBoundaryPLLoopDisk.project_protected_cut
    {X ι : Type*} [TopologicalSpace X] {Y F K : Set X}
    {e : ι → OpenPartialHomeomorph X V3}
    (hK : PLDomain e K) (hcut : Y ∩ frontier K = F) (hFY : F ⊆ Y)
    {d : ι × Y → OpenPartialHomeomorph Y V3}
    (hsource : ∀ k, MapsTo (Subtype.val : Y → X) (d k).source (e k.1).source)
    (hval : ∀ k, (d k : Y → V3) = (e k.1) ∘ Subtype.val)
    {P : Set Y} (hfront : frontier P = (Subtype.val : Y → X) ⁻¹' F)
    {base : (Subtype.val : Y → X) ⁻¹' F}
    (b : Dehn.MarkedBoundaryPLLoopDisk d P ((Subtype.val : Y → X) ⁻¹' F) base ⊥) :
    ∃ gamma : C(Q, F),
      PolyhedralPLInCharts e (fun z => (b.map z : X)) D ∧
      Topology.IsEmbedding (fun z : D => (b.map z : X)) ∧
      MapsTo (fun z => (b.map z : X)) D Y ∧
      (∀ z : Q, (b.map z : X) = (gamma z : X)) ∧
      (∀ z : D, (b.map z : X) ∈ F ↔ (z : V2) ∈ Q) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 ∧
      ((MapsTo (fun z => (b.map z : X)) D K ∧
          MapsTo (fun z => (b.map z : X)) (ball (0 : V2) 1) (interior K)) ∨
        (MapsTo (fun z => (b.map z : X)) D (interior K)ᶜ ∧
          MapsTo (fun z => (b.map z : X)) (ball (0 : V2) 1) Kᶜ)) := by
  obtain ⟨H, hH, hPL, hemb, hY, hrim, hproper⟩ :=
    exists_projected_proper_cut_map hFY hsource hval hfront b.piecewiseAffine
      b.embedding b.rim b.boundary_values b.whole_boundary_iff
  let gamma : C(Q, F) := (⟨H, H.continuous⟩ : C(_, F)).comp b.rim
  have hnontrivial : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map b.rim.continuous)) ≠ 1 := by
    intro h
    apply b.outside
    have hh := (b.basepath.whiskeredLoopClass_eq_one_iff
      (Dehn.squareRimLoop.map b.rim.continuous)).mpr h
    exact Subgroup.mem_bot.mpr hh
  have hpath : Dehn.squareRimLoop.map gamma.continuous =
      (Dehn.squareRimLoop.map b.rim.continuous).map H.continuous := by
    ext t
    rfl
  refine ⟨gamma, hPL, hemb, hY, hrim, hproper, ?_,
    hK.protected_disk_lies_on_one_side hcut hPL.continuousOn hY hproper⟩
  rw [hpath]
  exact fun h => hnontrivial ((H.loopClass_map_eq_one_iff _).mp h)

end PoincareConjecture.M76

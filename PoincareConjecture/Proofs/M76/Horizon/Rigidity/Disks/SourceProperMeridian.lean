import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.SourceMeridianFiniteBand
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.FiniteCylinderDiskCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.OriginalDiskParametrization

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L

theorem exists_source_proper_meridian
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (he : PLDomain e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ j : V2 → X, PolyhedralPLInCharts e j D ∧
      Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D R ∧
      (∀ x : D, j x ∈ frontier R ↔ (x : V2) ∈ Q) ∧
      ∀ x ∈ Q, j x = hamiltonStandardMeridianMap L x := by
  let T := (Fin 1 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 1)).toAddSubgroup
  let : CompactSpace T := hamiltonSolidTorusCircleEquiv.symm.compactSpace
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  have hR : IsCompact R := (isCompact_closedBall (0 : V2) 1).prod isCompact_univ
  have hRne : Set.Nonempty R := ⟨(0, 0), mem_closedBall_self zero_le_one, mem_univ _⟩
  obtain ⟨M⟩ := he.nonempty_original_finite_collar_model hR hRne
  obtain ⟨A, c, j, rim, hAB, hc, hcval, hj, hi, hjK, hjrim, _, hessential, hheight⟩ :=
    exists_source_meridian_finite_band_disk he M hd phi hphi F
  obtain ⟨D', S, gamma, hD, hDK, hfront, hgamma, hgamval⟩ :=
    M.exists_proper_disk_of_essential_cylindrical_rim
      c hc hAB j hj hi hjK rim hjrim hessential hheight
  apply M.exists_exact_original_disk hD hDK hfront gamma hgamma
    (hamiltonStandardMeridianMap L)
  · intro x hx
    exact ⟨sphere_subset_closedBall hx, mem_univ _⟩
  · intro x
    rw [hgamval, hcval]
    rfl

end PoincareConjecture.M76

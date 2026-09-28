import PoincareConjecture.Proofs.M76.Rigidity.OriginalMarkedProductConstruction
import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianBand

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "I" => Icc (-1 : ℝ) 1

private instance : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩

theorem exists_source_meridian_marked_product
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (he : PLDomain e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z)) (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z = hamiltonStandardMeridianMap L z)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      (∀ z ∈ Q, ∀ t ∈ I, P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-v) v))) := by
  let : CompactSpace T := hamiltonSolidTorusCircleEquiv.symm.compactSpace
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  have hR : IsCompact R := (isCompact_closedBall (0 : V2) 1).prod isCompact_univ
  have hcenter (z : V2) (hz : z ∈ Q) : hamiltonMeridianCutAmbientMap (z, 0) = j z :=
    (hamiltonMeridianBand_zero z).trans (hrim z hz).symm
  exact exists_small_original_marked_disk_product hR he hj hemb hDR hproper
    hamiltonMeridianCutAmbientMap (polyhedralPL_source_hamiltonMeridianBand hd phi hphi F)
    injOn_hamiltonMeridianBand mapsTo_hamiltonMeridianBand_frontier hcenter
    isOpen_hamiltonMeridianBand_image hU hDU

end PoincareConjecture.M76

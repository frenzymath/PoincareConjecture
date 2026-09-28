import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskCutComponents
import Mathlib.Analysis.Convex.Contractible









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

theorem OriginalDiskProduct.not_isConnected_cut_of_simplyConnected
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    [SimplyConnectedSpace R]
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) : ¬ IsConnected P.cutCarrier := by
  intro hconn
  obtain ⟨C, _, hends⟩ := P.exists_closedStrip_product
  obtain ⟨hc, _, _, hoverlap, hcover, _⟩ := P.cut_geometry hR hopen
  let : Nonempty Disk := ⟨⟨0, mem_closedBall_self zero_le_one⟩⟩
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  let : ConnectedSpace P.cutCarrier := isConnected_iff_connectedSpace.mp hconn
  let : PathConnectedSpace P.cutCarrier := PathConnectedSpace.of_locallyPathConnectedSpace
  have hpath : IsPathConnected P.cutCarrier :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hatt (z : Disk × unitInterval) :
      (C z : X) ∈ P.cutCarrier ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [← hends]
    exact ⟨fun hz => hoverlap.subset ⟨(C z).property, hz⟩,
      fun hz => (hoverlap.symm.subset hz).2⟩
  have hno := Poincare.Topology.not_simplyConnectedSpace_of_product_handle
    hc.isClosed (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    hpath C hatt
  change ¬ SimplyConnectedSpace (P.cutCarrier ∪ P.closedStrip : Set X) at hno
  rw [union_comm, hcover] at hno
  exact hno inferInstance

theorem OriginalDiskProduct.not_isConnected_cut_of_cube
    {ι : Type*} {e : ι → OpenPartialHomeomorph V3 V3} {j : V2 → V3}
    (P : OriginalDiskProduct e (closedBall (0 : V3) 1) j)
    (hopen : IsOpen ((Subtype.val : closedBall (0 : V3) 1 → V3) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) : ¬ IsConnected P.cutCarrier := by
  let : ContractibleSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).contractibleSpace
      ⟨0, mem_closedBall_self zero_le_one⟩
  exact P.not_isConnected_cut_of_simplyConnected (isCompact_closedBall _ _) hopen hPL

end PoincareConjecture.M76

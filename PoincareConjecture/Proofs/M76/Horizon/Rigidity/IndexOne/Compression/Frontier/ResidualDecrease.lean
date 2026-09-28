import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.ResidualCompressionDecrease
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_compressed_frontier_model
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (hN : IsCompact N) (he : PLDomain e N)
    (P : OriginalDiskProduct e N j)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (rim : C(Q, frontier N)) (hrim : ∀ z : Q, (rim z : X) = j z)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (oldModel : FrontierResidualModel e N (frontier N)) :
    ∃ newModel : FrontierResidualModel e P.cutCarrier (frontier P.cutCarrier),
      newModel.complexity < oldModel.complexity := by
  obtain ⟨hcompact, _, hfront, _, _, hne⟩ := P.cut_geometry hN hopen
  have hcut := P.plDomain_cut hN he hopen
  have hcap : P.map (0, (1 / 2 : ℝ)) ∈ P.endDisks := by
    exact ⟨(0, 1 / 2), ⟨mem_closedBall_self zero_le_one, Or.inr rfl⟩, rfl⟩
  have hfrontne : (frontier P.cutCarrier).Nonempty :=
    ⟨_, hfront.symm.subset (Or.inr hcap)⟩
  obtain ⟨newModel⟩ := hcut.nonempty_frontier_residual_model hcompact
    (hne.mono interior_subset) isClosed_empty isClosed_frontier (by simp)
    (empty_union _).symm hfrontne
  refine ⟨newModel, ?_⟩
  have hstrip : P.closedStrip ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  apply P.frontierResidualModel_complexity_decreases
    (U := univ) (univ_inter (frontier N)) (mapsTo_univ _ _)
    (P.isOpen_lateral_image he.closed (by norm_num : (1 / 2 : ℝ) ≤ 1) hopen)
    hfront he hN (union_subset he.closed.frontier_subset hstrip)
    hcut.closed.frontier_subset rim hrim hessential oldModel newModel

end PoincareConjecture.M76.HamiltonIntervalTorus

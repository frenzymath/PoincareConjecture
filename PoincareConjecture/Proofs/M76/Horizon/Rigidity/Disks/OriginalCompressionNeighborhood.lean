import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalBallNeighborhood
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFillingCutSide
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility













set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}


theorem OriginalDiskProduct.isPLIrreducible_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (hI : IsPLIrreducible e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    IsPLIrreducible e P.cutCarrier := by
  refine ⟨P.plDomain_cut hR hI.1 hopen, ?_⟩
  intro S hSK hs
  obtain ⟨B, hBR, ⟨b⟩⟩ := hI.2 S (hSK.trans (interior_mono sdiff_subset)) hs
  exact ⟨B, P.ball_subset_cut b hBR hSK, ⟨b⟩⟩



theorem exists_original_compression_neighborhood [CompactSpace X]
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ (P : OriginalDiskProduct e R j) (B S : Set X),
      MapsTo P.map (D ×ˢ I) U ∧
      PLDomain e P.closedStrip ∧
      Nonempty (ChartwisePLBall e P.closedStrip (frontier P.closedStrip)) ∧
      Nonempty (ChartwisePLBall e B S) ∧
      j '' D ⊆ P.closedStrip ∧ P.closedStrip ⊆ interior B ∧ B ⊆ U ∧
      P.closedStrip ∩ frontier R =
        P.map '' (Q ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧
      frontier P.closedStrip =
        (P.map '' (Q ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))) ∪ P.endDisks ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (IsPLIrreducible e R → IsPLIrreducible e P.cutCarrier) := by
  obtain ⟨P, hPU, hopen, hcut, hcompact, hint, hfront, hoverlap, hcover, hne⟩ :=
    exists_original_disk_cut_domain hR he hj hemb hDR hproper hU hDU
  obtain ⟨b⟩ := P.exists_closedStrip_ball
  have hPdomain := P.plDomain_closedStrip hR he hopen
  have hout : P.closedStripᶜ.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hint.subset hx).2⟩
  have hstripU : P.closedStrip ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPU ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨B, S, hb, hPB, hBU⟩ := b.exists_strict_ball_neighborhood hPdomain hout hU hstripU
  refine ⟨P, B, S, hPU, hPdomain, P.frontier_closedStrip.symm ▸ ⟨b⟩,
    hb, ?_, hPB, hBU, P.closedStrip_inter_frontier, P.frontier_closedStrip,
    hcut, hcompact, hfront, hoverlap, hcover, fun hI => P.isPLIrreducible_cut hR hI hopen⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨(z, 0), ⟨hz, by norm_num⟩, P.central z hz⟩

end PoincareConjecture.M76

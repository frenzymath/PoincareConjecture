import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalDiskCutDomainConstruction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalDiskStripDomain
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.OriginalFillingCutSide
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility

/-!
# Construct the actual support ball for a source compression disk

An entire proper embedded original-PL disk constructs a small product,
its complete strip ball and cut domain, and an enclosing PL support ball.
The complete strip, including its old-boundary annulus, lies in the
support interior. Every construction stays in the requested open set.
If the original region is irreducible, its disk cut is irreducible in
the same atlas. Embedded disk existence and map surgery remain separate.
See Waldhausen 1968, pp. 59--60.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- Actual proper-disk cuts inherit every original sphere filling. -/
theorem OriginalDiskProduct.isPLIrreducible_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (hI : IsPLIrreducible e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    IsPLIrreducible e P.cutCarrier := by
  refine ⟨P.plDomain_cut hR hI.1 hopen, ?_⟩
  intro S hSK hs
  obtain ⟨B, hBR, ⟨b⟩⟩ := hI.2 S (hSK.trans (interior_mono sdiff_subset)) hs
  exact ⟨B, P.ball_subset_cut b hBR hSK, ⟨b⟩⟩

/-- Construct a complete physical compression neighborhood from the
actual proper disk, retaining all old and new boundary pieces. -/
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

end PoincareMT.M76

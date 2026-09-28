import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapParametrization
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapOutsidePoint
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapRims
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.ChartwiseSphereDiskComplement
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem cap_component_not_sphere_of_graph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hS : S ⊆ Fnew) (hcomponent : ∀ x ∈ S, connectedComponentIn Fnew x = S)
    (b : Bool) (hcap : P.capDisk b ⊆ S) (hopposite : Disjoint S (P.capDisk (!b)))
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (phi : X → E) (hphi : Continuous phi) (hphiInj : InjOn phi S)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) :
    ¬ Nonempty (ChartwisePLSphere e S) := by
  rintro ⟨sphereModel⟩
  have hvS : MapsTo (P.capParameter b) D S := by
    intro z hz
    exact hcap ((P.capParameter_image_disk b).subset ⟨z, hz, rfl⟩)
  have hvInj : InjOn (P.capParameter b) D := by
    intro x hx y hy hxy
    exact congrArg Subtype.val ((P.embedding_capParameter b).injective
      (show P.capParameter b (⟨x, hx⟩ : D) = P.capParameter b (⟨y, hy⟩ : D) from hxy))
  have hout : (S \ P.capParameter b '' D).Nonempty := by
    rw [P.capParameter_image_disk]
    exact P.cap_complement_nonempty hcut hsmall hnew hcomponent b hcap
  obtain ⟨a, ha, hcontract, hgraph⟩ := sphereModel.exists_disk_complement
    phi hphi hphiInj hphiPL (P.capParameter b) (P.polyhedral_capParameter b) hvInj hvS hout
  rw [P.capParameter_image_disk, P.capParameter_image_rim] at hcontract
  let T := S \ (P.capDisk b \ P.capRimSet b)
  have hTF : T ⊆ F := P.cap_complement_subset_frontier_mark hcut hsmall hnew hS b hopposite
  obtain ⟨capRim, H, hvalues, _, hcapEssential⟩ :=
    P.exists_essential_lateral_rim hcut hsmall rim hrim hessential
      (if b then (1 / 2 : ℝ) else -(1 / 2)) (by cases b <;> norm_num)
  have hcapRim (u : Q) : (capRim u : X) ∈ P.capRimSet b := by
    rw [hvalues]
    exact ⟨(u, if b then (1 / 2 : ℝ) else -(1 / 2)), ⟨u.property, rfl⟩, rfl⟩
  let rimComp : C(Q, T) :=
    ⟨fun u => ⟨capRim u, hcap (P.capRimSet_subset_capDisk b (hcapRim u)),
      fun h => h.2 (hcapRim u)⟩,
      (continuous_subtype_val.comp capRim.continuous).subtype_mk _⟩
  let : ContractibleSpace T := hcontract
  have hnull := SimplyConnectedSpace.paths_homotopic
    (Dehn.squareRimLoop.map rimComp.continuous) (Path.refl (rimComp Dehn.squareRimBase))
  have hnullF : (Dehn.squareRimLoop.map capRim.continuous).Homotopic
      (Path.refl (capRim Dehn.squareRimBase)) := hnull.map (ContinuousMap.inclusion hTF)
  exact hcapEssential (Path.Homotopic.Quotient.eq.mpr hnullF)

theorem cap_component_not_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew S N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hS : S ⊆ Fnew) (hcomponent : ∀ x ∈ S, connectedComponentIn Fnew x = S)
    (b : Bool) (hcap : P.capDisk b ⊆ S) (hopposite : Disjoint S (P.capDisk (!b)))
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (hN : PLDomain e N) (hNc : IsCompact N) (hSN : S ⊆ N) :
    ¬ Nonempty (ChartwisePLSphere e S) := by
  have hNne : N.Nonempty := ((P.isConnected_capDisk b).nonempty.mono hcap).mono hSN
  obtain ⟨s, phi, K, A, H, g, HB, hphi, hphiPL, _, _, _, _, _, _, hH, _⟩ :=
    hN.exists_original_frontier_surface_model hNc hNne
  have hphiInj : InjOn phi S := by
    intro x hx y hy hxy
    have hh : H ⟨x, hSN hx⟩ = H ⟨y, hSN hy⟩ :=
      Subtype.ext ((hH ⟨x, hSN hx⟩).trans (hxy.trans (hH ⟨y, hSN hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  exact P.cap_component_not_sphere_of_graph hcut hsmall hnew hS hcomponent b hcap hopposite
    rim hrim hessential phi hphi hphiInj hphiPL

end PoincareConjecture.M76.OriginalDiskProduct

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskThreePorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskOneSideAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exterior_cap_component_remainders
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (he : PLDomain e R) (hK : PLDomain e K)
    (hKR : K ⊆ interior R) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfrontK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (owner : Bool) (k q : Bool → Set V3)
    (howner : ∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner)
    (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
      (sB owner).map '' q b = P.capRimSet b ∧
      ((sB owner).map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q b)
    (hcomp : ∀ b, IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b))
    (hkdis : Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false))
    (hcover : (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
      (P.map '' (Rim ×ˢ J)) = B owner)
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true))) :
    let D := fun b => connectedComponentIn P.cutCarrier (a b)
    let ret := fun b => (sB owner).map '' k b
    let T := fun b => D b ∩ (B (!owner) ∪ frontier R)
    (∀ b, IsCompact (ret b)) ∧ (∀ b, IsConnected (ret b)) ∧
      (∀ b, ret b ∩ P.closedStrip = P.capRimSet b) ∧
      (∀ b, (ret b \ P.capDisk b).Nonempty) ∧
      (∀ b, IsClosed (T b)) ∧
      (∀ b, Disjoint (ret b ∪ P.capDisk b) (T b)) ∧
      ∀ b, frontier (D b) = (ret b ∪ P.capDisk b) ∪ T b := by
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  let ret := fun b => (sB owner).map '' k b
  let N := fun b => ret b ∪ P.capDisk b
  let T := fun b => D b ∩ (B (!owner) ∪ frontier R)
  obtain ⟨hL, _, _, _, hLf⟩ := he.interior_removal_geometry hR hK hKR
  obtain ⟨hQ, _, hQf, hattach, _, _⟩ := P.cut_geometry hL hopen
  obtain ⟨hmarks, _, _, _, hNconn, _, hoppN, hKcut⟩ :=
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfrontK
      hsmall hstripK owner k q howner hk hcomp hkdis hcover
  have hrets (b : Bool) : ret b ∩ P.closedStrip = P.capRimSet b :=
    ((hmarks b).2.2.2.2.1).trans ((hmarks b).2.2.2.1)
  have hretc (b : Bool) : IsCompact (ret b) :=
    (hk b).1.isCompact.image_of_continuousOn
      ((sB owner).piecewiseAffine.continuousOn.mono (hk b).2.1)
  have hretconn (b : Bool) : IsConnected (ret b) :=
    (hk b).1.isConnected.image _ ((sB owner).piecewiseAffine.continuousOn.mono (hk b).2.1)
  have hsi : InjOn (sB owner).map Sphere := by
    intro x hx y hy hxy
    rw [(sB owner).map_eq ⟨x, hx⟩, (sB owner).map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val ((sB owner).parametrization.injective (Subtype.ext hxy))
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hretout (b : Bool) : (ret b \ P.capDisk b).Nonempty := by
    obtain ⟨z, hzk, hzq⟩ := (hk b).1.sdiff_nonempty
    refine ⟨(sB owner).map z, mem_image_of_mem _ hzk, ?_⟩
    intro hcap
    have hrim := (hrets b).subset ⟨mem_image_of_mem _ hzk, hcapstrip b hcap⟩
    obtain ⟨y, hyq, hyz⟩ := (hk b).2.2.1.symm.subset hrim
    exact hzq (hsi ((hk b).2.1 ((hk b).1.1 hyq)) ((hk b).2.1 hzk) hyz ▸ hyq)
  have hopeninside : P.openStrip ⊆ interior R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsmall ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hRf : frontier R \ P.openStrip = frontier R :=
    sdiff_eq_left.mpr (disjoint_left.mpr (fun _ hf ho => hf.2 (hopeninside ho)))
  have hQfront : frontier P.cutCarrier = ((B (!owner) ∪ N false) ∪ N true) ∪ frontier R := by
    rw [hQf, hLf, union_sdiff_distrib, hRf]
    calc
      ((frontier K \ P.openStrip) ∪ frontier R) ∪ P.endDisks =
          ((frontier K \ P.openStrip) ∪ P.endDisks) ∪ frontier R := by
        ext x
        simp only [mem_union]
        tauto
      _ = _ := congrArg (· ∪ frontier R) hKcut
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hNQ (b : Bool) : N b ⊆ P.cutCarrier := by
    apply subset_trans _ hQ.isClosed.frontier_subset
    rw [hQfront]
    cases b
    · exact subset_union_of_subset_left (subset_union_of_subset_left subset_union_right _) _
    · exact subset_union_of_subset_left subset_union_right _
  have hND (b : Bool) : N b ⊆ D b :=
    (hNconn b).isPreconnected.subset_connectedComponentIn (Or.inr (ha b)) (hNQ b)
  have hNinside (b : Bool) : N b ⊆ interior R := by
    rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · apply hKR
      apply hK.closed.frontier_subset
      have hxB : (sB owner).map z ∈ B owner := by
        rw [(sB owner).map_eq ⟨z, (hk b).2.1 hz⟩]
        exact ((sB owner).parametrization ⟨z, (hk b).2.1 hz⟩).property
      rw [hfrontK]
      cases owner
      · exact Or.inl hxB
      · exact Or.inr hxB
    · exact hsmall (cap_source_subset b hz)
  have hDc (b : Bool) : IsCompact (D b) :=
    isCompact_connectedComponentIn_of_mem hQ (hcapQ b (ha b))
  have hTc (b : Bool) : IsClosed (T b) :=
    (hDc b).isClosed.inter ((sB (!owner)).isCompact.isClosed.union isClosed_frontier)
  have hNT (b : Bool) : Disjoint (N b) (T b) := by
    apply disjoint_left.mpr
    rintro x hxN ⟨_, hxB | hxR⟩
    · exact disjoint_left.mp (hoppN b) hxB hxN
    · exact hxR.2 (hNinside b hxN)
  refine ⟨hretc, hretconn, hrets, hretout, hTc, hNT, ?_⟩
  intro b
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  obtain ⟨O, hO, hDO⟩ := exists_open_inter_of_relative_open
    (connectedComponentIn_subset P.cutCarrier (a b))
    (isOpen_preimage_connectedComponentIn (hcapQ b (ha b)))
  have hf : frontier (D b) = D b ∩ frontier P.cutCarrier :=
    frontier_eq_inter_of_eq_inter_open hQ.isClosed (hDc b).isClosed hO hDO
  change frontier (D b) = N b ∪ T b
  rw [hf, hQfront]
  ext x
  have hown : x ∈ N b → x ∈ D b := fun hx => hND b hx
  have hother : x ∈ D b → x ∉ N (!b) := by
    intro hx hy
    cases b
    · exact disjoint_left.mp hdis hx (hND true hy)
    · exact disjoint_left.mp hdis (hND false hy) hx
  cases b <;>
    simp only [T, Bool.not_false, Bool.not_true, mem_union, mem_inter_iff] at hown hother ⊢ <;> tauto

end PoincareConjecture.M76.OriginalDiskProduct

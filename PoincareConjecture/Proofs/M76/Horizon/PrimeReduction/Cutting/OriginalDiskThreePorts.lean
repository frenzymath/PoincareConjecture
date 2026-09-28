import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.GlobalExteriorDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorAnnulusDisks
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry










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

theorem three_connected_ports_of_retained_disks
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (he : PLDomain e R) (hK : PLDomain e K)
    (hKR : K ⊆ interior R) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfront : frontier K = B false ∪ B true)
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
      (P.map '' (Rim ×ˢ J)) = B owner) :
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b) ∧
        (sB owner).map '' q b = P.capRimSet b ∧
        ((sB owner).map '' k b) ∩ P.closedStrip = (sB owner).map '' q b ∧
        P.capDisk b ∩ K = (sB owner).map '' q b) ∧
      Disjoint ((sB owner).map '' k false) ((sB owner).map '' k true) ∧
      B owner \ P.openStrip = ((sB owner).map '' k false) ∪ ((sB owner).map '' k true) ∧
      Disjoint (B (!owner)) P.closedStrip ∧
      (∀ b, IsConnected (((sB owner).map '' k b) ∪ P.capDisk b)) ∧
      Disjoint (((sB owner).map '' k false) ∪ P.capDisk false)
        (((sB owner).map '' k true) ∪ P.capDisk true) ∧
      (∀ b, Disjoint (B (!owner)) (((sB owner).map '' k b) ∪ P.capDisk b)) ∧
      (frontier K \ P.openStrip) ∪ P.endDisks =
        (B (!owner) ∪ (((sB owner).map '' k false) ∪ P.capDisk false)) ∪
          (((sB owner).map '' k true) ∪ P.capDisk true) := by
  let ret := fun b => (sB owner).map '' k b
  have hretB (b : Bool) : ret b ⊆ B owner := by
    rintro x ⟨z, hz, rfl⟩
    rw [(sB owner).map_eq ⟨z, (hk b).2.1 hz⟩]
    exact ((sB owner).parametrization ⟨z, (hk b).2.1 hz⟩).property
  have hBK (b : Bool) : B b ⊆ K := by
    apply subset_trans _ hK.closed.frontier_subset
    rw [hfront]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hretK (b : Bool) : ret b ⊆ K := (hretB b).trans (hBK owner)
  have hbandB : P.map '' (Rim ×ˢ J) ⊆ B owner := (howner owner).mpr rfl
  have hrim (b : Bool) : (sB owner).map '' q b = P.capRimSet b :=
    (hk b).2.2.1
  have hcapend (b : Bool) : P.capDisk b ⊆ P.endDisks := by
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip :=
    (hcapend b).trans P.endDisks_subset_closedStrip
  have hretstrip (b : Bool) : ret b ∩ P.closedStrip = (sB owner).map '' q b := by
    apply Subset.antisymm
    · rintro x ⟨hxret, hxstrip⟩
      exact (hk b).2.2.2.subset ⟨hxret, hstripK.subset ⟨hxstrip, hretK b hxret⟩⟩
    · intro x hx
      have hr := (hk b).2.2.2.symm.subset hx
      exact ⟨hr.1, (hstripK.symm.subset hr.2).1⟩
  have hOldfront := (he.interior_removal_geometry hR hK hKR).2.2.2.2
  have hcapK (b : Bool) : P.capDisk b ∩ K = (sB owner).map '' q b := by
    rw [hrim]
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, rfl⟩, hxK⟩
      have hzfull := cap_source_subset b hz
      have hxfrontK : P.map z ∈ frontier K := by
        rw [hK.closed.frontier_eq]
        exact ⟨hxK, (P.inside hzfull).2⟩
      have hxfront : P.map z ∈ frontier (R ∩ (interior K)ᶜ) :=
        hOldfront.symm.subset (Or.inl hxfrontK)
      exact ⟨z, ⟨(P.proper z hzfull).mp hxfront, hz.2⟩, rfl⟩
    · intro x hx
      refine ⟨P.capRimSet_subset_capDisk b hx, ?_⟩
      have hxr : x ∈ (sB owner).map '' q b := (hrim b).symm.subset hx
      exact hretK b ((image_mono (hk b).1.1) hxr)
  have hretmiss (b : Bool) : Disjoint (ret b) P.openStrip := by
    apply disjoint_left.mpr
    intro x hxret hxopen
    have hxstrip : x ∈ P.closedStrip :=
      image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hxopen
    have hxr := (hrim b).subset ((hretstrip b).subset ⟨hxret, hxstrip⟩)
    have hxend := hcapend b (P.capRimSet_subset_capDisk b hxr)
    exact (P.closedStrip_sdiff_openStrip.symm.subset hxend).2 hxopen
  have hretain : B owner \ P.openStrip = ret false ∪ ret true := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxopen⟩
      rcases hcover.symm.subset hxB with (hxt | hxf) | hxband
      · exact Or.inr hxt
      · exact Or.inl hxf
      · obtain ⟨z, hz, rfl⟩ := hxband
        have hzedge : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
          by_contra h
          push Not at h
          exact hxopen ⟨z, ⟨sphere_subset_closedBall hz.1,
            lt_of_le_of_ne hz.2.1 h.1.symm, lt_of_le_of_ne hz.2.2 h.2⟩, rfl⟩
        rcases hzedge with heq | heq
        · apply Or.inl
          apply image_mono (hk false).1.1
          apply (hrim false).symm.subset
          exact ⟨z, ⟨hz.1, heq⟩, rfl⟩
        · apply Or.inr
          apply image_mono (hk true).1.1
          apply (hrim true).symm.subset
          exact ⟨z, ⟨hz.1, heq⟩, rfl⟩
    · rintro x (hx | hx)
      · exact ⟨hretB false hx, fun ho => disjoint_left.mp (hretmiss false) hx ho⟩
      · exact ⟨hretB true hx, fun ho => disjoint_left.mp (hretmiss true) hx ho⟩
  have hBopp : Disjoint (B (!owner)) (B owner) := by
    cases owner
    · exact hBdis.symm
    · exact hBdis
  have hoppstrip : Disjoint (B (!owner)) P.closedStrip := by
    apply disjoint_left.mpr
    intro x hxB hxstrip
    exact disjoint_left.mp hBopp hxB (hbandB (hstripK.subset ⟨hxstrip, hBK (!owner) hxB⟩))
  have hnewconn (b : Bool) : IsConnected (ret b ∪ P.capDisk b) := by
    have hretconn : IsConnected (ret b) :=
      (hk b).1.isConnected.image _ ((sB owner).piecewiseAffine.continuousOn.mono (hk b).2.1)
    apply hretconn.union _ (P.isConnected_capDisk b)
    obtain ⟨z, hz⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
    have hxr : P.map (z, if b then (1 / 2 : ℝ) else -(1 / 2)) ∈ P.capRimSet b :=
      ⟨(z, if b then (1 / 2 : ℝ) else -(1 / 2)), ⟨hz, rfl⟩, rfl⟩
    exact ⟨_, (image_mono (hk b).1.1) ((hrim b).symm.subset hxr),
      P.capRimSet_subset_capDisk b hxr⟩
  have hnewdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true) := by
    apply disjoint_left.mpr
    rintro x (hxf | hcf) (hxt | hct)
    · exact disjoint_left.mp hkdis hxt hxf
    · exact disjoint_left.mp hkdis
        ((image_mono (hk true).1.1) ((hcapK true).subset ⟨hct, hretK false hxf⟩)) hxf
    · exact disjoint_left.mp hkdis hxt
        ((image_mono (hk false).1.1) ((hcapK false).subset ⟨hcf, hretK true hxt⟩))
    · exact disjoint_left.mp (P.disjoint_capDisks false) hcf hct
  refine ⟨?_, hkdis.symm, hretain, hoppstrip, hnewconn, hnewdis, ?_, ?_⟩
  · intro b
    exact ⟨(hk b).1, (hk b).2.1, hcomp b, hrim b, hretstrip b, hcapK b⟩
  · intro b
    exact hBopp.mono_right (hretB b) |>.union_right (hoppstrip.mono_right (hcapstrip b))
  · have hBcover : frontier K = B (!owner) ∪ B owner := by
      rw [hfront]
      cases owner <;> simp [union_comm]
    have hoppopen : B (!owner) \ P.openStrip = B (!owner) := by
      apply sdiff_eq_left.mpr
      exact hoppstrip.mono_right (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
    rw [hBcover, union_sdiff_distrib, hoppopen, hretain, P.endDisks_eq_capDisks]
    ext x
    simp only [mem_union]
    tauto

theorem exists_original_three_connected_ports
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (he : PLDomain e R) (hK : PLDomain e K)
    (hKR : K ⊆ interior R) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfront : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J)) :
    ∃ (owner : Bool) (k q : Bool → Set V3),
      (∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner) ∧
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b) ∧
        (sB owner).map '' q b = P.capRimSet b ∧
        ((sB owner).map '' k b) ∩ P.closedStrip = (sB owner).map '' q b ∧
        P.capDisk b ∩ K = (sB owner).map '' q b) ∧
      Disjoint ((sB owner).map '' k false) ((sB owner).map '' k true) ∧
      B owner \ P.openStrip = ((sB owner).map '' k false) ∪ ((sB owner).map '' k true) ∧
      Disjoint (B (!owner)) P.closedStrip ∧
      (∀ b, IsConnected (((sB owner).map '' k b) ∪ P.capDisk b)) ∧
      Disjoint (((sB owner).map '' k false) ∪ P.capDisk false)
        (((sB owner).map '' k true) ∪ P.capDisk true) ∧
      (∀ b, Disjoint (B (!owner)) (((sB owner).map '' k b) ∪ P.capDisk b)) ∧
      (frontier K \ P.openStrip) ∪ P.endDisks =
        (B (!owner) ∪ (((sB owner).map '' k false) ∪ P.capDisk false)) ∪
          (((sB owner).map '' k true) ∪ P.capDisk true) := by
  obtain ⟨owner, g, k, q, C, howner, _, _, _, hk, hkdis, hcover, hprod⟩ :=
    P.exists_exterior_annulus_disks B sB he.compatible hBdis rfl hfront hsmall
  exact ⟨owner, k, q, howner,
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfront hsmall
      hstripK owner k q howner
      (fun b => ⟨(hk b).1, (hk b).2.1, (hk b).2.2.2.1, (hk b).2.2.2.2⟩)
      (fun b => (hprod b).1) hkdis hcover⟩

end PoincareConjecture.M76.OriginalDiskProduct

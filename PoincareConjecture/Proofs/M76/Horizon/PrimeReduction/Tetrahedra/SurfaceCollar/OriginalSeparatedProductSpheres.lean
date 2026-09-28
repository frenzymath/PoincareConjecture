import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalProductCircleSides
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_separated_end_spheres
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hproper : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim) :
    ∃ k q : Bool → Set V3,
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b) ∧
        s.map '' q b = P.map '' (Rim ×ˢ {if b then (1/2 : ℝ) else -(1/2)}) ∧
        (s.map '' k b) ∩ P.closedStrip = s.map '' q b) ∧
      Disjoint (s.map '' k true) (s.map '' k false) ∧
      ((s.map '' k true) ∪ (s.map '' k false)) ∪
        (P.map '' (Rim ×ˢ J)) = S ∧
      ∃ t : ∀ b, ChartwisePLSphere e ((s.map '' k b) ∪ P.capDisk b),
        (∀ b, EqOn (t b).map s.map (k b) ∧
          (t b).map '' (Sphere \ (k b \ q b)) = P.capDisk b) ∧
        Disjoint ((s.map '' k true) ∪ P.capDisk true)
          ((s.map '' k false) ∪ P.capDisk false) ∧
        (((s.map '' k true) ∪ P.capDisk true) ∪
          ((s.map '' k false) ∪ P.capDisk false)) \ P.closedStrip = S \ P.closedStrip := by
  classical
  have hsmall : Disk ×ˢ J ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hz,ht⟩
    exact ⟨hz,by constructor <;> linarith [ht.1,ht.2]⟩
  have hband : P.map '' (Rim ×ˢ J) ⊆ S := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hproper z (hsmall ⟨sphere_subset_closedBall hz.1,hz.2⟩)).mpr hz.1
  have hcontact : P.closedStrip ∩ S = P.map '' (Rim ×ˢ J) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,hz,rfl⟩,hS⟩
      exact ⟨z,⟨(hproper z (hsmall hz)).mp hS,hz.2⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩,
        hband (mem_image_of_mem _ hz)⟩
  obtain ⟨a,ha,hai,haimage,hamarks⟩ := P.exists_lateral_annulus
  have haS : MapsTo a (squareAnnulus 8 1) S :=
    fun x hx => hband (haimage.subset (mem_image_of_mem a hx))
  have hone : (1 : V2) ∈ Rim := by simp
  let pole : S := ⟨P.map ((1 : V2),3/4),
    (hproper _ ⟨sphere_subset_closedBall hone,by norm_num⟩).mpr hone⟩
  have hpole : (pole : X) ∉ a '' squareAnnulus 8 1 := by
    rw [haimage]
    rintro ⟨z,hz,hzmap⟩
    have heq := P.injective (hsmall ⟨sphere_subset_closedBall hz.1,hz.2⟩)
      ⟨sphere_subset_closedBall hone,by norm_num⟩ hzmap
    have hh := congrArg Prod.snd heq
    dsimp at hh
    linarith [hz.2.2]
  obtain ⟨_,k,q,_,_,_,_,_,hk,hdis,hcover,hprod⟩ :=
    s.exists_original_annulus_disks hcompat a ha hai haS pole hpole
  have hmark (b : Bool) : s.map '' q b =
      P.map '' (Rim ×ˢ {if b then (1/2 : ℝ) else -(1/2)}) :=
    (hk b).2.2.2.1.trans (hamarks b)
  have hretS (b : Bool) : s.map '' k b ⊆ S := by
    rintro _ ⟨x,hx,rfl⟩
    rw [s.map_eq ⟨x,(hk b).2.1 hx⟩]
    exact (s.parametrization ⟨x,(hk b).2.1 hx⟩).property
  have hmeet (b : Bool) : (s.map '' k b) ∩ P.closedStrip = s.map '' q b := by
    apply Subset.antisymm
    · intro x hx
      apply (hk b).2.2.2.2.subset
      exact ⟨hx.1,haimage.symm.subset (hcontact.subset ⟨hx.2,hretS b hx.1⟩)⟩
    · intro x hx
      have hh := (hk b).2.2.2.2.symm.subset hx
      exact ⟨hh.1,(hcontact.symm.subset (haimage.subset hh.2)).1⟩
  choose t ht htcap using fun b => P.exists_original_retained_end_cap s hcompat
    (hk b).1 (hk b).2.1 (hprod b).1 hcontact b (hmark b)
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply image_mono
    rintro z ⟨hz,ht⟩
    refine ⟨hz,?_⟩
    rw [show z.2 = if b then (1/2 : ℝ) else -(1/2) from ht]
    cases b <;> norm_num
  have hcapcontact (b : Bool) : P.capDisk b ∩ S ⊆ s.map '' q b := by
    rw [hmark b]
    rintro _ ⟨⟨z,hz,rfl⟩,hS⟩
    have hzfull : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
      refine ⟨hz.1,?_⟩
      rw [show z.2 = if b then (1/2 : ℝ) else -(1/2) from hz.2]
      cases b <;> norm_num
    exact ⟨z,⟨(hproper z hzfull).mp hS,hz.2⟩,rfl⟩
  have hcapdis : Disjoint (P.capDisk true) (P.capDisk false) := by
    apply disjoint_left.mpr
    rintro y ⟨z,hz,hzy⟩ ⟨w,hw,hwy⟩
    have heq := P.injective (hsmall (by exact ⟨hz.1,by rw [show z.2 = 1/2 from hz.2]; norm_num⟩))
      (hsmall (by exact ⟨hw.1,by rw [show w.2 = -(1/2) from hw.2]; norm_num⟩)) (hzy.trans hwy.symm)
    have hh := congrArg Prod.snd heq
    rw [show z.2 = 1/2 from hz.2,show w.2 = -(1/2) from hw.2] at hh
    norm_num at hh
  refine ⟨k,q,fun b => ⟨(hk b).1,(hk b).2.1,(hprod b).1,hmark b,hmeet b⟩,
    hdis,by simpa only [haimage] using hcover,t,fun b => ⟨ht b,htcap b⟩,?_,?_⟩
  · apply disjoint_left.mpr
    rintro x (hr | hc) (hr' | hc')
    · exact disjoint_left.mp hdis hr hr'
    · exact disjoint_left.mp hdis hr (image_mono (hk false).1.1
        (hcapcontact false ⟨hc',hretS true hr⟩))
    · exact disjoint_left.mp hdis (image_mono (hk true).1.1
        (hcapcontact true ⟨hc,hretS false hr'⟩)) hr'
    · exact disjoint_left.mp hcapdis hc hc'
  · apply Subset.antisymm
    · rintro x ⟨(hr | hc) | (hr | hc),hn⟩
      · exact ⟨hretS true hr,hn⟩
      · exact False.elim (hn (hcapstrip true hc))
      · exact ⟨hretS false hr,hn⟩
      · exact False.elim (hn (hcapstrip false hc))
    · rintro x ⟨hx,hn⟩
      refine ⟨?_,hn⟩
      rcases hcover.symm.subset hx with (ht | hf) | hb
      · exact Or.inl (Or.inl ht)
      · exact Or.inr (Or.inl hf)
      · exact False.elim (hn ((hcontact.symm.subset (haimage.subset hb)).1))

end PoincareConjecture.M76.OriginalDiskProduct

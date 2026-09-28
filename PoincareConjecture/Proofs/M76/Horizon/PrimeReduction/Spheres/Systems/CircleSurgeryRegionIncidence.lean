import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryWitnesses

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.circle_surgery_region_incidence_of_cut_witnesses
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (d : Bool → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d true ∪ d false = Sphere) (hinter : d true ∩ d false = r)
    (p : Bool → V3) (hp : ∀ b, p b ∈ d b \ r)
    {U : Set X} (houtside : ∀ b, s.map (p b) ∉ U)
    (k q : Bool → Set V3) (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b))
    (hkS : ∀ b, k b ⊆ Sphere) (hkr : ∀ b, Disjoint (k b) r)
    {band : Set V3} (hcover : (k true ∪ k false) ∪ band = Sphere)
    (hkband : ∀ b, k b ∩ band = q b) (hbandU : s.map '' band ⊆ U)
    {region : Set X} (hclosed : IsClosed region) (hRU : region ⊆ U)
    (hfrontier : frontier region ∩ S = s.map '' band) :
    region ∩ S = s.map '' band ∧ Disjoint (interior region) S ∧
      ∀ b, region ∩ (s.map '' k b) = s.map '' q b := by
  have hbandS : band ⊆ Sphere := subset_union_right.trans hcover.subset
  have hqband (b : Bool) : q b ⊆ band := (hkband b).symm.subset.trans inter_subset_right
  obtain hwitness := circle_cut_witnesses_meet_retained_disks s.map d hd hwhole hinter
    p hp houtside k q hk hkS hkr hcover hqband hbandU
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hcont : ContinuousOn s.map Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp s.parametrization.continuous).congr
      (fun x => (s.map_eq x).symm)
  have himage : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [s.map_eq ⟨x,hx⟩]
      exact (s.parametrization ⟨x,hx⟩).property
    · intro x hx
      obtain ⟨y,hy⟩ := s.parametrization.surjective ⟨x,hx⟩
      exact ⟨y,y.property,(s.map_eq y).trans (congrArg Subtype.val hy)⟩
  have hbandR : s.map '' band ⊆ region := by
    rw [←hfrontier]
    exact inter_subset_left.trans hclosed.frontier_subset
  have hkoutside (b : Bool) : s.map '' (k b \ q b) ⊆ regionᶜ := by
    have hksub : k b \ q b ⊆ Sphere := sdiff_subset.trans (hkS b)
    have hpre := ((hk b).isConnected_sdiff.image s.map
      (hcont.mono hksub)).isPreconnected
    apply hpre.m76_subset_of_disjoint_frontier hclosed.isOpen_compl
    · rw [frontier_compl]
      apply Set.disjoint_left.mpr
      rintro y hy ⟨x,hx,rfl⟩
      have hxS : s.map x ∈ S := himage.subset ⟨x,hksub hx,rfl⟩
      obtain ⟨z,hz,hzx⟩ := hfrontier.subset ⟨hy,hxS⟩
      have hzx' := hsi (hbandS hz) (hksub hx) hzx
      exact hx.2 ((hkband b).subset ⟨hx.1,hzx' ▸ hz⟩)
    · obtain ⟨i,hi,hnot⟩ := hwitness b
      exact ⟨s.map (p i),⟨p i,hi,rfl⟩,fun hx => hnot (hRU hx)⟩
  have hincidence : region ∩ S = s.map '' band := by
    apply Subset.antisymm
    · rintro y ⟨hyR,hyS⟩
      obtain ⟨x,hx,rfl⟩ := himage.symm.subset hyS
      have hxcover := hcover.symm.subset hx
      rcases hxcover with (hx | hx) | hx
      · by_cases hq : x ∈ q true
        · exact ⟨x,hqband true hq,rfl⟩
        · exact (hkoutside true ⟨x,⟨hx,hq⟩,rfl⟩ hyR).elim
      · by_cases hq : x ∈ q false
        · exact ⟨x,hqband false hq,rfl⟩
        · exact (hkoutside false ⟨x,⟨hx,hq⟩,rfl⟩ hyR).elim
      · exact ⟨x,hx,rfl⟩
    · exact fun _ hx => ⟨hbandR hx,himage.subset (image_mono hbandS hx)⟩
  refine ⟨hincidence,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxR hxS
    have hxband := hincidence.subset ⟨interior_subset hxR,hxS⟩
    exact (hfrontier.symm.subset hxband).1.2 hxR
  · intro b
    apply Subset.antisymm
    · rintro y ⟨hyR,x,hx,rfl⟩
      have hxS : s.map x ∈ S := himage.subset ⟨x,hkS b hx,rfl⟩
      obtain ⟨z,hz,hzx⟩ := hincidence.subset ⟨hyR,hxS⟩
      have heq := hsi (hbandS hz) (hkS b hx) hzx
      exact ⟨x,(hkband b).subset ⟨hx,heq ▸ hz⟩,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨hbandR ⟨x,hqband b hx,rfl⟩,x,(hk b).1 hx,rfl⟩

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRetainedDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryRegionIncidence

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_circle_collar_region_incidence
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (d : Bool → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d true ∪ d false = Sphere) (hinter : d true ∩ d false = r)
    (p : Bool → V3) (hp : ∀ b, p b ∈ d b \ r)
    {U : Set X} (houtside : ∀ b, s.map (p b) ∉ U)
    {β : ℝ} (hβ : 0 < β) (sigma : C3 → V3)
    (hSigma : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc 0 β))
    (hMap : MapsTo sigma (signedTubeDiamond ×ˢ Icc 0 β) (Q.target ∩ Q.symm ⁻¹' U))
    (hMember : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β,
      z.1.2 = 0 → Q.symm (sigma z) ∈ S)
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (hrimage : s.map '' r = (fun t => Q.symm (sigma ((0, 0), t))) '' Icc 0 β)
    {region : Set X} (hclosed : IsClosed region) (hRU : region ⊆ U)
    (hfrontier : frontier region ∩ S =
      (fun z : P2 => Q.symm (sigma ((z.1, 0), z.2))) ''
        (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) :
    ∃ (φ : P2 → V3) (k : Bool → Set V3),
      FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) ∧
      MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere ∧
      (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
        s.map (φ z) = Q.symm (sigma ((z.1, 0), z.2))) ∧
      ((fun t : ℝ => φ (0, t)) '' Icc 0 β = r) ∧
      (∀ b,
        let q := (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β
        IsFinitePLBallPair P2 (k b) q ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ q)) q ∧
        s.map '' q = (fun t => Q.symm (sigma ((if b then 1 / 4 else -1 / 4, 0), t))) '' Icc 0 β ∧
        k b ∩ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = q ∧
        Disjoint (k b) r ∧ region ∩ (s.map '' k b) = s.map '' q) ∧
      Disjoint (k true) (k false) ∧
      (k true ∪ k false) ∪ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = Sphere ∧
      region ∩ S = (fun z : P2 => Q.symm (sigma ((z.1, 0), z.2))) ''
        (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) ∧ Disjoint (interior region) S := by
  have hSigmaCompact := hSigma.isCompact.image_of_continuousOn hSigma.continuousOn
  obtain ⟨J, hJ, hSJ, hJQ⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hSigmaCompact Q.open_target
      (by rintro _ ⟨x, hx, rfl⟩; exact (hMap hx).1)
  obtain ⟨φ, k, hφ, hφS, hφval, hk, hkdis, hkwhole⟩ :=
    s.exists_circle_collar_retained_disks Q hQ J hJ hJQ hβ sigma hSigma
      (fun x hx => interior_subset (hSJ ⟨x, hx, rfl⟩)) hMember hfib
  let q : Bool → Set V3 := fun b =>
    (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β
  let band := φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)
  have hquarter {z : P2} (hz : z ∈ Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) :
      z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hbandImage : s.map '' band =
      (fun z : P2 => Q.symm (sigma ((z.1, 0), z.2))) ''
        (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) := by
    rw [show s.map '' band = (s.map ∘ φ) '' _ by exact (image_comp _ _ _).symm]
    exact image_congr (fun x hx => hφval x (hquarter hx))
  have hbandU : s.map '' band ⊆ U := by
    rw [hbandImage]
    rintro _ ⟨z, hz, rfl⟩
    have hdom : ((z.1, 0), z.2) ∈ signedTubeDiamond ×ˢ Icc 0 β := by
      simpa only [signedSheetStripMap_apply, Fin.reduceEq, if_false] using
        signedSheetStripMap_mem (1 : Fin 2) (hquarter hz)
    exact (hMap hdom).2
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x, hx⟩, s.map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have haxisS : (fun t : ℝ => φ (0, t)) '' Icc 0 β ⊆ Sphere := by
    rintro _ ⟨t, ht, rfl⟩
    exact hφS ⟨by norm_num, ht⟩
  have hrS : r ⊆ Sphere := (hd true).1.trans (subset_union_left.trans hwhole.subset)
  have haxisEq : (fun t : ℝ => φ (0, t)) '' Icc 0 β = r := by
    apply (hsi.image_eq_image_iff haxisS hrS).mp
    rw [hrimage, image_image]
    exact image_congr (fun t ht => hφval (0, t) ⟨by norm_num, ht⟩)
  have hkr (b : Bool) : Disjoint (k b) r := by
    rw [← haxisEq]
    exact (hk b).2.2.2.2.2.2.2
  obtain ⟨hincidence, hInterior, hretained⟩ :=
    s.circle_surgery_region_incidence_of_cut_witnesses d hd hwhole hinter p hp houtside
      k q (fun b => (hk b).1) (fun b => (hk b).2.1) hkr hkwhole
      (fun b => (hk b).2.2.2.2.2.2.1) hbandU hclosed hRU (hfrontier.trans hbandImage.symm)
  refine ⟨φ, k, hφ, hφS, hφval, haxisEq, ?_, hkdis, hkwhole,
    hincidence.trans hbandImage, hInterior⟩
  intro b
  exact ⟨(hk b).1, (hk b).2.1, (hk b).2.2.1, (hk b).2.2.2.2.2.1,
    (hk b).2.2.2.2.2.2.1, hkr b, hretained b⟩

end PoincareConjecture.M76

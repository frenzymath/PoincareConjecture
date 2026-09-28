import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedInteriorProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedPortMiddleDisk

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_two_port_face_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d bd : Set P2} {region band S F circle : Set X} (caps : Bool → Set X)
    (hd : IsFinitePLBallPair P2 d bd)
    (C : (d × unitInterval) ≃ₜ region) (p : P3 → X)
    (hp : PolyhedralPLInCharts e p (d ×ˢ Icc (0 : ℝ) 1))
    (hpval : ∀ z : (d ×ˢ Icc (0 : ℝ) 1 : Set P3),
      p z = (C ((Homeomorph.Set.prod _ _) z) : X))
    (hcaps : ∀ b z, (C z : X) ∈ caps b ↔ z.2 = if b then 1 else 0)
    (hfront : frontier region = band ∪ (caps true ∪ caps false))
    (hcontact : region ∩ S = band)
    (hF : IsClosed F) (hcapF : ∀ b, Disjoint (caps b) F)
    (hbandF : band ∩ F = circle) :
    ∃ ρ : V2 × ℝ → X,
      PolyhedralPLInCharts e ρ (closedBall (0 : V2) 1 ×ˢ I) ∧
      InjOn ρ (closedBall (0 : V2) 1 ×ˢ I) ∧
      MapsTo ρ (closedBall (0 : V2) 1 ×ˢ I) region ∧
      (∀ z ∈ closedBall (0 : V2) 1 ×ˢ I,
        ρ z ∈ S ↔ z.1 ∈ sphere (0 : V2) 1) ∧
      (∀ b : Bool,
        Disjoint (ρ '' (closedBall (0 : V2) 1 ×ˢ
          {if b then (1/2 : ℝ) else -(1/2)})) F) ∧
      (ρ '' (sphere (0 : V2) 1 ×ˢ J)) ∩ F = circle ∧
      region ∩ F ⊆ ρ '' (closedBall (0 : V2) 1 ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := by
  have hpi : InjOn p (d ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw hzw
    have hh : C ((Homeomorph.Set.prod _ _) ⟨z,hz⟩) =
        C ((Homeomorph.Set.prod _ _) ⟨w,hw⟩) := Subtype.ext
      ((hpval ⟨z,hz⟩).symm.trans (hzw.trans (hpval ⟨w,hw⟩)))
    exact congrArg Subtype.val ((Homeomorph.Set.prod _ _).injective (C.injective hh))
  have hpimage : p '' (d ×ˢ Icc (0 : ℝ) 1) = region := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [hpval ⟨z,hz⟩]
      exact (C _).property
    · intro x hx
      let z : (d ×ˢ Icc (0 : ℝ) 1 : Set P3) :=
        (Homeomorph.Set.prod _ _).symm (C.symm ⟨x,hx⟩)
      refine ⟨z,z.property,?_⟩
      rw [hpval]
      change (C ((Homeomorph.Set.prod d (Icc (0 : ℝ) 1))
        ((Homeomorph.Set.prod d (Icc (0 : ℝ) 1)).symm (C.symm ⟨x,hx⟩))) : X) = x
      rw [Homeomorph.apply_symm_apply,C.apply_symm_apply]
  have hproper (z : P3) (hz : z ∈ d ×ˢ Ioo (0 : ℝ) 1) :
      p z ∈ S ↔ z.1 ∈ bd :=
    (original_two_port_level_disk caps hd C p hp hpval hcaps hfront hcontact
      hz.2.1 hz.2.2).2.2.2.1 z.1 hz.1
  have hends (z : P3) (hz : z ∈ d ×ˢ Icc (0 : ℝ) 1)
      (ht : z.2 = 0 ∨ z.2 = 1) : p z ∉ F := by
    rw [hpval ⟨z,hz⟩]
    rcases ht with ht | ht
    · apply disjoint_left.mp (hcapF false)
      apply (hcaps false _).mpr
      exact Subtype.ext ht
    · apply disjoint_left.mp (hcapF true)
      apply (hcaps true _).mpr
      exact Subtype.ext ht
  obtain ⟨a,ρ,ha,has,hρ,hρi,hwhole,_,hρproper,hcapsF,hall,hband⟩ :=
    exists_positioned_interior_product hd p hp hpi hproper hF hends
  refine ⟨ρ,hρ,hρi,?_,hρproper,hcapsF,?_,?_⟩
  · intro z hz
    apply hpimage.subset
    obtain ⟨w,hw,heq⟩ := hwhole.subset ⟨z,hz,rfl⟩
    exact ⟨w,⟨hw.1,by linarith [hw.2.1],by linarith [hw.2.2]⟩,heq⟩
  · simpa only [hpimage,hcontact,hbandF] using hband
  · simpa only [hpimage] using hall

end PoincareConjecture.M76

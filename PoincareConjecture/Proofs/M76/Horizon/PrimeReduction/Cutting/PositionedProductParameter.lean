import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedProductInnerLevels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedProductTimeParameter
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.OriginalUnitDiskParameter
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_positioned_product_parameter
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {D r : Set E} {S F : Set X}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D r)
    (p : E × ℝ → X) (hp : PolyhedralPLInCharts e p (D ×ˢ Icc (0 : ℝ) 1))
    (hpi : InjOn p (D ×ˢ Icc (0 : ℝ) 1))
    (hproper : ∀ z ∈ D ×ˢ Icc (0 : ℝ) 1, p z ∈ S ↔ z.1 ∈ r)
    (hF : IsClosed F)
    (hends : ∀ z ∈ D ×ˢ Icc (0 : ℝ) 1, z.2 = 0 ∨ z.2 = 1 → p z ∉ F) :
    ∃ (δ : ℝ) (ρ : V2 × ℝ → X),
      0 < δ ∧ δ ≤ 1/4 ∧
      PolyhedralPLInCharts e ρ (Disk ×ˢ I) ∧ InjOn ρ (Disk ×ˢ I) ∧
      ρ '' (Disk ×ˢ I) = p '' (D ×ˢ Icc (0 : ℝ) 1) ∧
      ρ '' (Rim ×ˢ I) = p '' (r ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ Disk ×ˢ I, ρ z ∈ S ↔ z.1 ∈ Rim) ∧
      ρ '' (Disk ×ˢ J) = p '' (D ×ˢ Icc δ (1-δ)) ∧
      ρ '' (Rim ×ˢ J) = p '' (r ×ˢ Icc δ (1-δ)) ∧
      (∀ b : Bool, ρ '' (Disk ×ˢ {if b then (1/2 : ℝ) else -(1/2)}) =
        p '' (D ×ˢ {if b then 1-δ else δ})) ∧
      (∀ z ∈ Disk ×ˢ I, ρ z ∈ F → -(1/2 : ℝ) < z.2 ∧ z.2 < 1/2) ∧
      (∀ b : Bool, Disjoint (ρ '' (Disk ×ˢ {if b then (1/2 : ℝ) else -(1/2)})) F) ∧
      (p '' (D ×ˢ Icc (0 : ℝ) 1)) ∩ F ⊆ ρ '' (Disk ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let p₀ : D × unitInterval → X := fun z => p (z.1,z.2)
  have hp₀ : Continuous p₀ := hp.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property,z.2.property⟩)
  obtain ⟨δ,hδ,hδsmall,hinner,havoid⟩ := exists_positioned_product_inner_levels p₀ hp₀ hF
    (fun z hz => hends _ ⟨z.1.property,z.2.property⟩ (by
      rcases hz with hz | hz
      · exact Or.inl (congrArg Subtype.val hz)
      · exact Or.inr (congrArg Subtype.val hz)))
  obtain ⟨φ,Ht,hφ,hHt,hHtval,hmono,hleft,hright,hlo,hhi,hφJ,hφJo⟩ :=
    exists_positioned_product_time_parameter hδ (by linarith)
  obtain ⟨H₀,hH₀,hHrim⟩ := hD.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let H := H₀.symm
  obtain ⟨u,hu,huval⟩ := hH₀.symm
  have huD : MapsTo u Disk D := fun z hz => (huval ⟨z,hz⟩) ▸ (H ⟨z,hz⟩).property
  have hur (z : V2) (hz : z ∈ Disk) : u z ∈ r ↔ z ∈ Rim := by
    have hh := hHrim (H ⟨z,hz⟩)
    rw [H₀.apply_symm_apply,frontier_closedBall _ one_ne_zero] at hh
    rwa [huval] at hh
  have hui : InjOn u Disk := by
    intro z hz w hw hzw
    have hh : H ⟨z,hz⟩ = H ⟨w,hw⟩ := Subtype.ext
      ((huval ⟨z,hz⟩).trans (hzw.trans (huval ⟨w,hw⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have huImage : u '' Disk = D := by
    apply Subset.antisymm (image_subset_iff.mpr huD)
    intro z hz
    refine ⟨H.symm ⟨z,hz⟩,(H.symm ⟨z,hz⟩).property,?_⟩
    rw [←huval,H.apply_symm_apply]
  have hurImage : u '' Rim = r := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (hur z (sphere_subset_closedBall hz)).mpr hz
    · intro z hz
      obtain ⟨w,hw,hwz⟩ := huImage.symm.subset (hD.1 hz)
      exact ⟨w,(hur w hw).mp (hwz.symm ▸ hz),hwz⟩
  have hφImage : φ '' I = Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨t,ht,rfl⟩
      exact (hHtval ⟨t,ht⟩) ▸ (Ht ⟨t,ht⟩).property
    · intro t ht
      refine ⟨Ht.symm ⟨t,ht⟩,(Ht.symm ⟨t,ht⟩).property,?_⟩
      rw [←hHtval,Ht.apply_symm_apply]
  let m := Prod.map u φ
  let ρ := p ∘ m
  have hm : MapsTo m (Disk ×ˢ I) (D ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    exact ⟨huD hz.1,hφImage.subset (mem_image_of_mem φ hz.2)⟩
  have hρ : PolyhedralPLInCharts e ρ (Disk ×ˢ I) := by
    have h := hu.prodMap hφ
    obtain ⟨K,hK,hKs,_⟩ := h
    exact hKs ▸ hp.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hu.prodMap hφ)
      (fun z hz => hm (hKs.subset hz))
  have hρi : InjOn ρ (Disk ×ˢ I) := by
    intro z hz w hw hzw
    have hh := hpi (hm hz) (hm hw) hzw
    exact Prod.ext (hui hz.1 hw.1 (congrArg Prod.fst hh))
      (hmono.injective (congrArg Prod.snd hh))
  have himage (A : Set V2) (J' : Set ℝ) : ρ '' (A ×ˢ J') = p '' ((u '' A) ×ˢ (φ '' J')) := by
    change (p ∘ Prod.map u φ) '' (A ×ˢ J') = _
    rw [image_comp,prodMap_image_prod]
  have hface (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) (hzF : ρ z ∈ F) :
      -(1/2 : ℝ) < z.2 ∧ z.2 < 1/2 := by
    have hh := hinner (⟨u z.1,huD hz.1⟩,⟨φ z.2,(hm hz).2⟩) hzF
    constructor
    · apply hmono.lt_iff_lt.mp
      simpa only [hlo] using hh.1
    · apply hmono.lt_iff_lt.mp
      simpa only [hhi] using hh.2
  refine ⟨δ,ρ,hδ,hδsmall,hρ,hρi,?_,?_,?_,?_,?_,?_,hface,?_,?_⟩
  · rw [himage,huImage,hφImage]
  · rw [himage,hurImage,hφImage]
  · intro z hz
    exact (hproper _ (hm hz)).trans (hur z.1 hz.1)
  · rw [himage,huImage,hφJ]
  · rw [himage,hurImage,hφJ]
  · intro b
    rw [himage,huImage,image_singleton]
    cases b <;> simp only [Bool.false_eq_true,reduceIte,hlo,hhi]
  · intro b
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxF
    have hzt : z.2 = if b then (1/2 : ℝ) else -(1/2) := hz.2
    have hzI : z.2 ∈ I := by rw [hzt]; cases b <;> norm_num
    have hh := hface z ⟨hz.1,hzI⟩ hxF
    cases b <;> simp only [Bool.false_eq_true,reduceIte] at hzt <;> linarith [hh.1,hh.2]
  · rintro x ⟨hx,hxF⟩
    obtain ⟨z,hz,rfl⟩ := (show ρ '' (Disk ×ˢ I) = p '' (D ×ˢ Icc (0 : ℝ) 1) by
      rw [himage,huImage,hφImage]).symm.subset hx
    exact ⟨z,⟨hz.1,hface z hz hxF⟩,rfl⟩

end PoincareConjecture.M76

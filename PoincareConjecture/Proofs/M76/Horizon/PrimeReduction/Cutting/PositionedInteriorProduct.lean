import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedProductParameter

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_positioned_interior_product
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {D r : Set E} {S F : Set X}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D r)
    (p : E × ℝ → X) (hp : PolyhedralPLInCharts e p (D ×ˢ Icc (0 : ℝ) 1))
    (hpi : InjOn p (D ×ˢ Icc (0 : ℝ) 1))
    (hproper : ∀ z ∈ D ×ˢ Ioo (0 : ℝ) 1, p z ∈ S ↔ z.1 ∈ r)
    (hF : IsClosed F)
    (hends : ∀ z ∈ D ×ˢ Icc (0 : ℝ) 1, z.2 = 0 ∨ z.2 = 1 → p z ∉ F) :
    ∃ (a : ℝ) (ρ : V2 × ℝ → X), 0 < a ∧ a < 1/2 ∧
      PolyhedralPLInCharts e ρ (Disk ×ˢ I) ∧ InjOn ρ (Disk ×ˢ I) ∧
      ρ '' (Disk ×ˢ I) = p '' (D ×ˢ Icc a (1-a)) ∧
      ρ '' (Rim ×ˢ I) = p '' (r ×ˢ Icc a (1-a)) ∧
      (∀ z ∈ Disk ×ˢ I, ρ z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ b : Bool, Disjoint (ρ '' (Disk ×ˢ {if b then (1/2 : ℝ) else -(1/2)})) F) ∧
      (p '' (D ×ˢ Icc (0 : ℝ) 1)) ∩ F ⊆ ρ '' (Disk ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) ∧
      (ρ '' (Rim ×ˢ J)) ∩ F = (p '' (D ×ˢ Icc (0 : ℝ) 1)) ∩ S ∩ F := by
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
  let a := δ
  have ha : 0 < a := hδ
  have haSmall : a < 1/2 := by dsimp [a]; linarith
  let w : ℝ := 1-2*a
  have hw : 0 < w := by dsimp [w]; linarith
  let time : ℝ → ℝ := fun t => a+w*t
  have htime : time '' Icc (0 : ℝ) 1 = Icc a (1-a) := by
    have hc : Continuous time := by dsimp [time]; fun_prop
    have hm : StrictMono time := by intro x y hxy; dsimp [time]; nlinarith [mul_pos hw (sub_pos.mpr hxy)]
    rw [hc.image_Icc_of_strictMono hm]
    congr 1 <;> dsimp [time,w] <;> ring
  let A : (E × ℝ) →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ (E × ℝ) a +
        w • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hAval (z : E × ℝ) : A z = (z.1,time z.2) := rfl
  have hAmap : MapsTo A (D ×ˢ Icc (0 : ℝ) 1) (D ×ˢ Ioo (0 : ℝ) 1) := by
    intro z hz
    refine ⟨hz.1,?_,?_⟩ <;> change _ < _ <;> dsimp [A,time,w] <;>
      nlinarith [hz.2.1,hz.2.2,mul_nonneg hw.le hz.2.1,mul_nonneg hw.le (sub_nonneg.mpr hz.2.2)]
  have hAmap' : MapsTo A (D ×ˢ Icc (0 : ℝ) 1) (D ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨(hAmap hz).1,(hAmap hz).2.1.le,(hAmap hz).2.2.le⟩
  let p' := p ∘ A
  have hp' : PolyhedralPLInCharts e p' (D ×ˢ Icc (0 : ℝ) 1) := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
      hD.prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    exact hKs ▸ hp.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,K.affineOnFaces_affine A⟩ (fun z hz => hAmap' (hKs.subset hz))
  have hpi' : InjOn p' (D ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz v hv h
    have hh := hpi (hAmap' hz) (hAmap' hv) h
    rw [hAval, hAval] at hh
    have hf := congrArg Prod.fst hh
    apply Prod.ext
    · exact hf
    have ht := congrArg Prod.snd hh
    change a+w*z.2 = a+w*v.2 at ht
    exact mul_left_cancel₀ hw.ne' (add_left_cancel ht)
  have hproper' (z) (hz : z ∈ D ×ˢ Icc (0 : ℝ) 1) : p' z ∈ S ↔ z.1 ∈ r :=
    hproper _ (hAmap hz)
  have hends' (z) (hz : z ∈ D ×ˢ Icc (0 : ℝ) 1)
      (ht : z.2 = 0 ∨ z.2 = 1) : p' z ∉ F := by
    apply havoid (⟨z.1,hz.1⟩,⟨time z.2,(hAmap' hz).2⟩)
    rcases ht with ht | ht
    · left; dsimp [time,a]; rw [ht]; ring
    · right; dsimp [time,w,a]; rw [ht]; ring
  have himage (B : Set E) : p' '' (B ×ˢ Icc (0 : ℝ) 1) = p '' (B ×ˢ Icc a (1-a)) := by
    have hAA : (A : E × ℝ → E × ℝ) = Prod.map id time := rfl
    rw [show p' = p ∘ A from rfl,image_comp,hAA,prodMap_image_prod,image_id,htime]
  obtain ⟨_,ρ,_,_,hρ,hρi,hwhole,hlateral,hρproper,_,_,_,_,hcaps,hinside⟩ :=
    exists_positioned_product_parameter hD p' hp' hpi' hproper' hF hends'
  have hfaces : (p '' (D ×ˢ Icc (0 : ℝ) 1)) ∩ F ⊆ p' '' (D ×ˢ Icc (0 : ℝ) 1) := by
    rintro x ⟨⟨z,hz,rfl⟩,hzF⟩
    rw [himage]
    have hh := hinner (⟨z.1,hz.1⟩,⟨z.2,hz.2⟩) hzF
    exact ⟨z,⟨hz.1,hh.1.le,hh.2.le⟩,rfl⟩
  have hρsub : ρ '' (Disk ×ˢ I) ⊆ p '' (D ×ˢ Icc (0 : ℝ) 1) := by
    rw [hwhole,himage]
    exact image_mono (prod_mono subset_rfl (Icc_subset_Icc ha.le (by linarith)))
  have hall : (p '' (D ×ˢ Icc (0 : ℝ) 1)) ∩ F ⊆
      ρ '' (Disk ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := fun x hx => hinside ⟨hfaces hx,hx.2⟩
  refine ⟨a,ρ,ha,haSmall,hρ,hρi,hwhole.trans (himage D),hlateral.trans (himage r),
    hρproper,hcaps,hall,?_⟩
  apply Subset.antisymm
  · rintro x ⟨⟨z,hz,rfl⟩,hzF⟩
    have hzI : z ∈ Disk ×ˢ I := ⟨sphere_subset_closedBall hz.1,by
      constructor <;> linarith [hz.2.1,hz.2.2]⟩
    exact ⟨⟨hρsub ⟨z,hzI,rfl⟩,(hρproper z hzI).mpr hz.1⟩,hzF⟩
  · rintro x ⟨⟨hx,hxS⟩,hxF⟩
    obtain ⟨z,hz,rfl⟩ := hall ⟨hx,hxF⟩
    have hzI : z ∈ Disk ×ˢ I := ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
    exact ⟨⟨z,⟨(hρproper z hzI).mp hxS,hz.2.1.le,hz.2.2.le⟩,rfl⟩,hxF⟩

end PoincareConjecture.M76

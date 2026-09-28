import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.CircleCapAttachment
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

private noncomputable def circleSphereBandCoordinates (β : ℝ) : P2 →ᴬ[ℝ] C3 :=
  (((1/4:ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.prod
    (ContinuousAffineMap.const ℝ P2 0)).prod
      ((β/32) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

private theorem circleSphereBandCoordinates_apply (β : ℝ) (z : P2) :
    circleSphereBandCoordinates β z = ((z.2/4,0),β/32*z.1) := by
  ext <;> simp [circleSphereBandCoordinates] <;> ring

theorem exists_circle_sphere_band_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0))) :
    let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
    ∃ c : squareAnnulus 8 1 ≃ₜ band,
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4*8)) (u : Icc (-1:ℝ) 1),
        (c ⟨annulusMap 8 (by norm_num) ((s:AddCircle (4*8:ℝ)),u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) =
            τ ((u/4,0),β/32*s) := by
  classical
  dsimp only
  let : Fact (0 < (4*8:ℝ)) := ⟨by norm_num⟩
  let C := circleSphereBandCoordinates β
  have hCval (z : P2) : C z = ((z.2/4,0),β/32*z.1) :=
    circleSphereBandCoordinates_apply β z
  have hCmap : MapsTo C (Icc 0 (4*8) ×ˢ Icc (-1:ℝ) 1)
      (signedTubeDiamond ×ˢ Icc 0 β) := by
    rintro ⟨s,u⟩ ⟨hs,hu⟩
    rw [hCval]
    refine ⟨(signedTubeDiamond_coordinate_iff _).mpr ?_,?_,?_⟩
    · simp only [abs_zero,add_zero,abs_div]
      norm_num
      have := abs_le.mpr hu
      linarith
    · exact mul_nonneg (by positivity) hs.1
    · dsimp
      nlinarith [hs.2]
  have hC : FinitePiecewiseAffineOn C (Icc 0 (4*8) ×ˢ Icc (-1:ℝ) 1) := by
    have hbox := (isFinitePLBallPair_Icc (by norm_num : (0:ℝ)<4*8)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1:ℝ)<1))
    obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ := hbox
    exact ⟨J,hJ,hJs,J.affineOnFaces_affine C⟩
  have hψ := hτ.comp hC hCmap
  have hfib' : ∀ x ∈ Icc 0 (4*8) ×ˢ Icc (-1:ℝ) 1,
      ∀ y ∈ Icc 0 (4*8) ×ˢ Icc (-1:ℝ) 1,
      (τ ∘ C) x = (τ ∘ C) y ↔ x.2 = y.2 ∧
        (x.1:AddCircle (4*8:ℝ)) = (y.1:AddCircle (4*8:ℝ)) := by
    intro x hx y hy
    have ht (s t : ℝ) : β/32*s = β/32*t ↔ s=t :=
      mul_right_inj' (by positivity)
    have hzero (s : ℝ) : β/32*s=0 ↔ s=0 := by
      simpa only [mul_zero] using ht s 0
    have hend (s : ℝ) : β/32*s=β ↔ s=4*8 := by
      have hv : β/32*(4*8)=β := by ring
      simpa only [hv] using ht s (4*8)
    rw [Function.comp_apply,Function.comp_apply,hfib _ (hCmap hx) _ (hCmap hy),
      hCval,hCval,AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1]
    simp only [Prod.mk.injEq,and_true]
    rw [div_left_inj' (by norm_num : (4:ℝ)≠0),ht,hzero,hend,hend,hzero]
  obtain ⟨c,hc,hci,hperiod,_⟩ := _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
    (by norm_num : (0:ℝ)<1) (by norm_num : (4:ℝ)*1<8) (τ ∘ C) hψ hfib'
  have himage : (τ ∘ C) '' (Icc 0 (4*8) ×ˢ Icc (-1:ℝ) 1) =
      (fun z : P2 => τ ((z.1,0),z.2)) ''
        (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨(z.2/4,β/32*z.1),⟨⟨?_,?_⟩,(hCmap hz).2⟩,?_⟩
      · dsimp
        linarith [hz.2.1]
      · dsimp
        linarith [hz.2.2]
      · exact congrArg τ (hCval z).symm
    · rintro _ ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
      refine ⟨(32*(t/β),4*u),⟨⟨mul_nonneg (by norm_num) (div_nonneg ht.1 hβ.le),?_⟩,
        ⟨by dsimp; linarith [hu.1],by dsimp; linarith [hu.2]⟩⟩,?_⟩
      · have := (div_le_one hβ).mpr ht.2
        dsimp
        nlinarith
      · change τ (C _) = _
        rw [hCval]
        congr 1
        ext <;> dsimp <;> field_simp
  let c' := c.trans (Homeomorph.setCongr himage)
  refine ⟨c',hc.setCongr rfl himage,(hc.setCongr rfl himage).symm,?_⟩
  intro s hs u
  exact (hperiod s hs u).trans (congrArg τ (hCval (s,u)))

theorem exists_circle_surgery_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    {M : Set E}
    (hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ M ↔ z.1.2 = 0)
    (caps : Bool → Set E)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b)
      ((fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcapM : ∀ b, caps b ∩ M =
      (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)
    (hdis : Disjoint (caps true) (caps false)) :
    let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
    let boundary := band ∪ (caps true ∪ caps false)
    IsFinitePLBallPair P2 (caps true ∪ band)
        ((fun t => τ ((-1/4,0),t)) '' Icc 0 β) ∧
      (caps true ∪ band) ∩ caps false =
        (fun t => τ ((-1/4,0),t)) '' Icc 0 β ∧
      boundary ∩ M = band ∧
      ∃ H : boundary ≃ₜ frontier (TriangularRoofModel.halfBall 1),
        H.IsFinitePL ∧
        (∀ x : boundary, (x:E) ∈ caps true ∪ band ↔ (H x:C3) ∈ TriangularRoofModel.cap 1) ∧
        (∀ x : boundary, (x:E) ∈ caps false ↔ (H x:C3) ∈ TriangularRoofModel.disk) := by
  classical
  dsimp only
  let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
    (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
  let q : Bool → Set E := fun b =>
    (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β
  have hbandM : band ⊆ M := by
    rintro _ ⟨z,hz,rfl⟩
    apply (hsphere _ ⟨(signedTubeDiamond_coordinate_iff _).mpr ?_,hz.2⟩).mpr rfl
    rw [abs_zero,add_zero,abs_le]
    constructor <;> linarith [hz.1.1,hz.1.2]
  have hqband (b : Bool) : q b ⊆ band := by
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨(if b then 1/4 else -1/4,t),⟨by cases b <;> norm_num,ht⟩,rfl⟩
  have hmeet (b : Bool) : caps b ∩ band = q b := by
    apply Subset.antisymm
    · exact fun _ hy => (hcapM b).subset ⟨hy.1,hbandM hy.2⟩
    · exact fun _ hy => ⟨(hcaps b).1 hy,hqband b hy⟩
  obtain ⟨c,hc,hci,hperiod⟩ := exists_circle_sphere_band_annulus hβ τ hτ hfib
  have hhalf : IsFinitePLBallPair P2 (caps true ∪ band) (q false) := by
    apply attach_periodic_annulus (hcaps true) (hmeet true) c hc
      (fun z : P2 => τ ((z.2/4,0),β/32*z.1)) hperiod
    · simpa using cap_circle_period_rescaling hβ τ ((1/4:ℝ),0)
    · simpa [q] using cap_circle_period_rescaling hβ τ ((-1/4:ℝ),0)
  have hbetween : (caps true ∪ band) ∩ caps false = q false := by
    rw [union_inter_distrib_right,hdis.inter_eq,empty_union,inter_comm]
    exact hmeet false
  obtain ⟨H,hH,hHb,hHd⟩ := hhalf.exists_sphere_model_of_disk_union (hcaps false) hbetween
  have hunion : (caps true ∪ band) ∪ caps false = band ∪ (caps true ∪ caps false) := by
    rw [union_comm (caps true) band,union_assoc]
  refine ⟨hhalf,hbetween,?_,(Homeomorph.setCongr hunion.symm).trans H,
    hH.setCongr hunion rfl,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨hx,hxM⟩
      rcases hx with hx | hx | hx
      · exact hx
      · exact hqband true ((hcapM true).subset ⟨hx,hxM⟩)
      · exact hqband false ((hcapM false).subset ⟨hx,hxM⟩)
    · exact fun hx => ⟨Or.inl hx,hbandM hx⟩
  · intro x
    exact hHb ⟨x,hunion.symm.subset x.property⟩
  · intro x
    exact hHd ⟨x,hunion.symm.subset x.property⟩

end PoincareConjecture.M76

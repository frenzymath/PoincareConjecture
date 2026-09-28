import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

noncomputable def taperingCapStrip (β : ℝ) (side positive : Bool) : P2 →ᴬ[ℝ] C3 :=
  let x : P2 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ P2 (1 / 8) -
    ((1 / 8 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let y : P2 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ P2 (1 / 4) +
    ((1 / 4 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  ((if positive then x else -x).prod (if side then y else -y)).prod
    ((β / 32) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

theorem taperingCapStrip_apply (β : ℝ) (side positive : Bool) (p : P2) :
    taperingCapStrip β side positive p =
      ((if positive then (1 - p.2) / 8 else -(1 - p.2) / 8,
        if side then (p.2 + 1) / 4 else -(p.2 + 1) / 4), β / 32 * p.1) := by
  cases side <;> cases positive <;> ext <;> simp [taperingCapStrip] <;> ring

theorem taperingCapStrip_mapsTo {β : ℝ} (hβ : 0 < β) (side positive : Bool) :
    MapsTo (taperingCapStrip β side positive) (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
      (signedTubeDiamond ×ˢ Icc 0 β) := by
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  rw [taperingCapStrip_apply]
  refine ⟨(signedTubeDiamond_coordinate_iff _).mpr ?_, ?_, ?_⟩
  · have h₁ : 0 ≤ 1 - u := by linarith [hu.2]
    have h₂ : 0 ≤ u + 1 := by linarith [hu.1]
    cases side <;> cases positive <;>
      simp only [Bool.false_eq_true, if_false, if_true, abs_div, abs_neg,
        abs_of_nonneg h₁, abs_of_nonneg h₂] <;>
      norm_num <;> linarith [hu.1, hu.2]
  · change 0 ≤ β / 32 * s
    exact mul_nonneg (by positivity) hs.1
  · change β / 32 * s ≤ β
    nlinarith [hs.2]

private theorem taperingCapStrip_finitePL (β : ℝ) (side positive : Bool) :
    FinitePiecewiseAffineOn (taperingCapStrip β side positive)
      (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) := by
  have hbox := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 8)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (taperingCapStrip β side positive)⟩

private theorem taperingCapStrip_fibers
    {X : Type*} {β : ℝ} (hβ : 0 < β) (τ : C3 → X)
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (side positive : Bool) :
    ∀ p ∈ Icc 0 (4 * 8) ×ˢ Icc (-1) 1, ∀ q ∈ Icc 0 (4 * 8) ×ˢ Icc (-1) 1,
      (τ ∘ taperingCapStrip β side positive) p = (τ ∘ taperingCapStrip β side positive) q ↔
        p.2 = q.2 ∧ (p.1 : AddCircle (4 * 8 : ℝ)) = (q.1 : AddCircle (4 * 8 : ℝ)) := by
  intro p hp q hq
  let : Fact (0 < (4 * 8 : ℝ)) := ⟨by norm_num⟩
  have hxy : (taperingCapStrip β side positive p).1 =
      (taperingCapStrip β side positive q).1 ↔ p.2 = q.2 := by
    rw [taperingCapStrip_apply, taperingCapStrip_apply]
    constructor
    · intro h
      have hy := congrArg Prod.snd h
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at hy <;>
        linarith
    · intro h
      rw [h]
  have ht (s t : ℝ) : β / 32 * s = β / 32 * t ↔ s = t :=
    mul_right_inj' (by positivity)
  have hzero (s : ℝ) : β / 32 * s = 0 ↔ s = 0 := by
    simpa only [mul_zero] using ht s 0
  have hend (s : ℝ) : β / 32 * s = β ↔ s = 4 * 8 := by
    have hv : β / 32 * (4 * 8) = β := by ring
    simpa only [hv] using ht s (4 * 8)
  rw [Function.comp_apply, Function.comp_apply,
    hfib _ (taperingCapStrip_mapsTo hβ side positive hp)
      _ (taperingCapStrip_mapsTo hβ side positive hq), hxy,
    AddCircle.coe_eq_coe_iff_eq_or_endpoints hp.1 hq.1]
  change p.2 = q.2 ∧
    (β / 32 * p.1 = β / 32 * q.1 ∨
      (β / 32 * p.1 = 0 ∧ β / 32 * q.1 = β) ∨
      (β / 32 * p.1 = β ∧ β / 32 * q.1 = 0)) ↔ _
  rw [ht, hzero, hend, hend, hzero]

theorem exists_tapering_cap_annuli
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (side : Bool) :
    let B : Bool → Set E := fun positive =>
      (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
    let q : Set E := (fun s : ℝ => τ ((0, if side then 1 / 2 else -1 / 2), β / 32 * s)) ''
      Icc 0 (4 * 8)
    ∃ c : ∀ positive : Bool, squareAnnulus 8 1 ≃ₜ B positive,
      (∀ positive, (c positive).IsFinitePL ∧ (c positive).symm.IsFinitePL ∧
        (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
          (c positive ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
            _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) =
            τ (taperingCapStrip β side positive (s, u))) ∧
        B positive ⊆ τ '' (signedTubeDiamond ×ˢ Icc 0 β) ∧
        B positive ∩ (τ '' {z | z ∈ signedTubeDiamond ×ˢ Icc 0 β ∧ z.1.1 = 0}) = q ∧
        B positive ∩ (τ '' {z | z ∈ signedTubeDiamond ×ˢ Icc 0 β ∧ z.1.2 = 0}) =
          (fun s : ℝ => τ ((if positive then 1 / 4 else -1 / 4, 0), β / 32 * s)) '' Icc 0 (4 * 8)) ∧
      B true ∩ B false = q := by
  classical
  dsimp only
  let B : Bool → Set E := fun positive =>
    (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
  let q : Set E := (fun s : ℝ => τ ((0, if side then 1 / 2 else -1 / 2), β / 32 * s)) '' Icc 0 (4 * 8)
  have hφ (positive : Bool) : FinitePiecewiseAffineOn (τ ∘ taperingCapStrip β side positive)
      (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) :=
    hτ.comp (taperingCapStrip_finitePL β side positive) (taperingCapStrip_mapsTo hβ side positive)
  choose c hc hci hperiod hdepth using fun positive =>
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
      (τ ∘ taperingCapStrip β side positive) (hφ positive)
      (taperingCapStrip_fibers hβ τ hfib side positive)
  have hinner (positive : Bool) (s : ℝ) :
      taperingCapStrip β side positive (s, 1) =
        ((0, if side then 1 / 2 else -1 / 2), β / 32 * s) := by
    cases side <;> cases positive <;> norm_num [taperingCapStrip_apply]
  have houter (positive : Bool) (s : ℝ) :
      taperingCapStrip β side positive (s, -1) =
        ((if positive then 1 / 4 else -1 / 4, 0), β / 32 * s) := by
    cases side <;> cases positive <;> norm_num [taperingCapStrip_apply]
  have hqB (positive : Bool) : q ⊆ B positive := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(s, 1), ⟨hs, by norm_num⟩, congrArg τ (hinner positive s)⟩
  have hqface : q ⊆ τ '' {z | z ∈ signedTubeDiamond ×ˢ Icc 0 β ∧ z.1.1 = 0} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨taperingCapStrip β side true (s, 1),
      ⟨taperingCapStrip_mapsTo hβ side true ⟨hs, by norm_num⟩, ?_⟩,
      congrArg τ (hinner true s)⟩
    rw [hinner]
  refine ⟨c, ?_, ?_⟩
  · intro positive
    refine ⟨hc positive, hci positive, hperiod positive, ?_, ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, taperingCapStrip_mapsTo hβ side positive hp, rfl⟩
    · apply Subset.antisymm
      · rintro y ⟨⟨p, hp, hpy⟩, z, ⟨hz, hz0⟩, hzy⟩
        have he := ((hfib _ (taperingCapStrip_mapsTo hβ side positive hp) z hz).mp
          (hpy.trans hzy.symm)).1
        have hn := congrArg Prod.fst he
        rw [taperingCapStrip_apply] at hn
        have hu : p.2 = 1 := by
          cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hn <;>
            rw [hz0] at hn <;> linarith
        refine ⟨p.1, hp.1, ?_⟩
        change τ (taperingCapStrip β side positive p) = y at hpy
        have hpv : p = (p.1, 1) := Prod.ext rfl hu
        rw [hpv, hinner] at hpy
        exact hpy
      · exact subset_inter (hqB positive) hqface
    · apply Subset.antisymm
      · rintro y ⟨⟨p, hp, hpy⟩, z, ⟨hz, hz0⟩, hzy⟩
        have he := ((hfib _ (taperingCapStrip_mapsTo hβ side positive hp) z hz).mp
          (hpy.trans hzy.symm)).1
        have hn := congrArg Prod.snd he
        rw [taperingCapStrip_apply] at hn
        have hu : p.2 = -1 := by
          cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at hn <;>
            rw [hz0] at hn <;> linarith
        refine ⟨p.1, hp.1, ?_⟩
        change τ (taperingCapStrip β side positive p) = y at hpy
        have hpv : p = (p.1, -1) := Prod.ext rfl hu
        rw [hpv, houter] at hpy
        exact hpy
      · rintro _ ⟨s, hs, rfl⟩
        refine ⟨⟨(s, -1), ⟨hs, by norm_num⟩, congrArg τ (houter positive s)⟩,
          taperingCapStrip β side positive (s, -1),
          ⟨taperingCapStrip_mapsTo hβ side positive ⟨hs, by norm_num⟩, ?_⟩,
          congrArg τ (houter positive s)⟩
        rw [houter]
  · apply Subset.antisymm
    · rintro y ⟨⟨p, hp, hpy⟩, q', hq', hqy⟩
      have he := ((hfib _ (taperingCapStrip_mapsTo hβ side true hp)
        _ (taperingCapStrip_mapsTo hβ side false hq')).mp (hpy.trans hqy.symm)).1
      have hn := congrArg Prod.fst he
      rw [taperingCapStrip_apply, taperingCapStrip_apply] at hn
      change (1 - p.2) / 8 = -(1 - q'.2) / 8 at hn
      have hu : p.2 = 1 := by linarith [hp.2.2, hq'.2.2]
      refine ⟨p.1, hp.1, ?_⟩
      change τ (taperingCapStrip β side true p) = y at hpy
      have hpv : p = (p.1, 1) := Prod.ext rfl hu
      rw [hpv, hinner] at hpy
      exact hpy
    · exact subset_inter (hqB true) (hqB false)

theorem cap_circle_period_rescaling {X : Type*} {β : ℝ} (hβ : 0 < β)
    (τ : C3 → X) (v : P2) :
    (fun s : ℝ => τ (v, β / 32 * s)) '' Icc 0 (4 * 8) =
      (fun t : ℝ => τ (v, t)) '' Icc 0 β := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨β / 32 * s, ⟨mul_nonneg (by positivity) hs.1, ?_⟩, rfl⟩
    nlinarith [hs.2]
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨32 * (t / β), ⟨mul_nonneg (by norm_num) (div_nonneg ht.1 hβ.le), ?_⟩, ?_⟩
    · have hquot : t / β ≤ 1 := (div_le_one hβ).mpr ht.2
      nlinarith
    · have hval : β / 32 * (32 * (t / β)) = t := by field_simp
      exact congrArg (fun s => τ (v, s)) hval

end PoincareConjecture.M76

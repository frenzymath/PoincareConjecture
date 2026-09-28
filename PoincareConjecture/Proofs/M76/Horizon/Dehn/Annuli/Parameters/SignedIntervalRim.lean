import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleHomeomorphLift
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.FinitePLPeriodLift
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CutRectangleExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "C" => AddCircle (4 * (8 : ℝ))

private theorem exists_interval_homeomorph {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f I) (hm : StrictMonoOn f I)
    (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ∃ e : I ≃ₜ I, e.IsFinitePL ∧ ∀ t : I, (e t : ℝ) = f t := by
  have himage : f '' I = I := by
    simpa only [h0, h1] using hf.continuousOn.image_Icc_of_monotoneOn
      zero_le_one hm.monotoneOn
  obtain ⟨e, he, hev⟩ := hf.exists_homeomorph_image hm.injOn
  exact ⟨e.trans (Homeomorph.setCongr himage), he.setCongr rfl himage, hev⟩

theorem exists_signed_interval_rim (q : C ≃ₜ C) {u : ℝ}
    (hu : u ∈ Ioo (-(3 / 2 : ℝ)) (3 / 2))
    (hqPL : FinitePiecewiseAffineOn
      (fun s : ℝ ↦ annulusMap 8 (by norm_num) (q ((32 * s : ℝ) : C), u)) I) :
    ∃ (b : ℝ) (positive : Bool) (e : I ≃ₜ I), b ∈ Ico 0 32 ∧ e.IsFinitePL ∧
      (e ⟨0, by norm_num⟩ : ℝ) = 0 ∧ (e ⟨1, by norm_num⟩ : ℝ) = 1 ∧
      ∀ s : I, q ((32 * (s : ℝ) : ℝ) : C) =
        ((b + (if positive then 32 * (e s : ℝ) else -(32 * (e s : ℝ))) : ℝ) : C) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let b : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 (q 0)
  have hb : b ∈ Ico 0 32 := by
    have h := (AddCircle.equivIco (4 * (8 : ℝ)) 0 (q 0)).property
    change 0 ≤ b ∧ b < 0 + 4 * 8 at h
    norm_num at h
    exact h
  have hbq : (b : C) = q 0 := AddCircle.coe_equivIco
  obtain ⟨L, hL0, hLq⟩ := AddCircle.exists_real_homeomorph_lift q b hbq
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc zero_lt_one
  have hLP : FinitePiecewiseAffineOn (fun s : ℝ ↦ L (32 * s)) I := by
    rw [← hKI]
    apply finitePiecewiseAffineOn_real_rim_lift (L := 8) (d := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) hu K hK
      (L.continuous.comp (continuous_const.mul continuous_id)).continuousOn
    rw [hKI]
    exact hqPL.congr (fun s _ ↦ by dsimp only [Function.comp_apply, Pi.mul_apply, id]; rw [hLq])
  rcases AddCircle.real_homeomorph_lift_orientation q L hLq with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · let f : ℝ → ℝ := fun s ↦ (L (32 * s) - b) / 32
    have hf : FinitePiecewiseAffineOn f I := (hLP.postcomp
      ((1 / 32 : ℝ) • (ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ b))).congr
      (fun s _ ↦ by change (1 / 32) * (L (32 * s) - b) = (L (32 * s) - b) / 32; ring)
    have hm' : StrictMonoOn f I := by
      intro x _ y _ hxy
      exact div_lt_div_of_pos_right (sub_lt_sub_right (hm (by linarith)) b) (by norm_num)
    have h0 : f 0 = 0 := by simp [f, hL0]
    have h1 : f 1 = 1 := by
      have hh := hp 0
      norm_num [hL0] at hh
      dsimp [f]
      norm_num [hh]
    obtain ⟨e, he, hev⟩ := exists_interval_homeomorph hf hm' h0 h1
    refine ⟨b, true, e, hb, he, (hev _).trans h0, (hev _).trans h1, ?_⟩
    intro s
    rw [← hLq, hev]
    congr 1
    dsimp [f]
    ring
  · let f : ℝ → ℝ := fun s ↦ (b - L (32 * s)) / 32
    have hf : FinitePiecewiseAffineOn f I := (hLP.postcomp
      ((1 / 32 : ℝ) • (ContinuousAffineMap.const ℝ ℝ b - ContinuousAffineMap.id ℝ ℝ))).congr
      (fun s _ ↦ by change (1 / 32) * (b - L (32 * s)) = (b - L (32 * s)) / 32; ring)
    have hm' : StrictMonoOn f I := by
      intro x _ y _ hxy
      exact div_lt_div_of_pos_right (sub_lt_sub_left (hm (by linarith)) b) (by norm_num)
    have h0 : f 0 = 0 := by simp [f, hL0]
    have h1 : f 1 = 1 := by
      have hh := hp 0
      norm_num [hL0] at hh
      dsimp [f]
      norm_num [hh]
    obtain ⟨e, he, hev⟩ := exists_interval_homeomorph hf hm' h0 h1
    refine ⟨b, false, e, hb, he, (hev _).trans h0, (hev _).trans h1, ?_⟩
    intro s
    rw [← hLq, hev]
    congr 1
    dsimp [f]
    ring

end PoincareConjecture.M76.Dehn

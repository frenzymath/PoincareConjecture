import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.SourceBridge
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.ArcExtension



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_actual_arm_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {c : P2 → E} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ∃ p : I ≃ₜ (c '' arm u), p.IsFinitePL ∧ ∀ t : I, (p t : E) = c ((t : ℝ), u) := by
  obtain ⟨hArm, p, hp, hpval⟩ := exists_arm_parameter u
  have hArmS : arm u ⊆ source := fun x hx ↦ ⟨hx.1, (hx.2 : x.2 = u) ▸ hu⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hArm
  have hcArm : FinitePiecewiseAffineOn c (arm u) := by
    rw [← hKs]
    exact hc.restrict K hK (hKs.subset.trans hArmS)
  obtain ⟨H, hH, hHval⟩ := hcArm.exists_homeomorph_image (hci.mono hArmS)
  refine ⟨p.trans H, hp.trans hH, ?_⟩
  intro t
  simp only [Homeomorph.trans_apply, hHval, hpval]

theorem exists_disk_identification_center_to_far_arm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {c₀ : P2 → E} {c₁ : P2 → F}
    (hc₀ : FinitePiecewiseAffineOn c₀ source) (hi₀ : InjOn c₀ source)
    (hc₁ : FinitePiecewiseAffineOn c₁ source) (hi₁ : InjOn c₁ source)
    {D U : Set E} {B V : Set F}
    (hD : IsFinitePLBallPair P2 D (U ∪ c₀ '' arm 0))
    (hB : IsFinitePLBallPair P2 B (V ∪ c₁ '' arm 1))
    (hU : IsFinitePLBallPair ℝ U {c₀ (0, 0), c₀ (1, 0)})
    (hV : IsFinitePLBallPair ℝ V {c₁ (0, 1), c₁ (1, 1)})
    (hUW : U ∩ (c₀ '' arm 0) = {c₀ (0, 0), c₀ (1, 0)})
    (hVZ : V ∩ (c₁ '' arm 1) = {c₁ (0, 1), c₁ (1, 1)}) :
    ∃ H : D ≃ₜ B, H.IsFinitePL ∧
      (∀ t : I, ∀ hx : c₀ ((t : ℝ), 0) ∈ D,
        (H ⟨c₀ ((t : ℝ), 0), hx⟩ : F) = c₁ ((t : ℝ), 1)) ∧
      (∀ x : D, (x : E) ∈ U ↔ (H x : F) ∈ V) ∧
      ∀ x : D, (x : E) ∈ c₀ '' arm 0 ↔ (H x : F) ∈ c₁ '' arm 1 := by
  obtain ⟨p₀, hp₀, hp₀val⟩ := exists_actual_arm_parameter hc₀ hi₀ (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
  obtain ⟨p₁, hp₁, hp₁val⟩ := exists_actual_arm_parameter hc₁ hi₁ (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
  let r := p₀.symm.trans p₁
  have hr : r.IsFinitePL := hp₀.symm.trans hp₁
  have hrval (t : I) (ht : c₀ ((t : ℝ), 0) ∈ c₀ '' arm 0) :
      (r ⟨c₀ ((t : ℝ), 0), ht⟩ : F) = c₁ ((t : ℝ), 1) := by
    have hpoint : (⟨c₀ ((t : ℝ), 0), ht⟩ : c₀ '' arm 0) = p₀ t :=
      Subtype.ext (hp₀val t).symm
    rw [hpoint]
    simpa only [r, Homeomorph.trans_apply, p₀.symm_apply_apply] using hp₁val t
  have hcenter : IsFinitePLBallPair ℝ (c₀ '' arm 0) {c₀ (0, 0), c₀ (1, 0)} := by
    have h := (exists_arm_parameter 0).1.image_of_subset hc₀
      (fun x hx ↦ halfSource_subset_source false (arm_zero_subset_halfSource false hx)) hi₀
    simpa only [image_pair] using h
  obtain ⟨H, hH, hHr, hHU, hHW⟩ := exists_disk_homeomorph_prescribed_arc
    hD hB hU hcenter hV hUW hVZ r hr (hrval 0 _) (hrval 1 _)
  refine ⟨H, hH, ?_, hHU, hHW⟩
  intro t ht
  have hx : c₀ ((t : ℝ), 0) ∈ c₀ '' arm 0 :=
    ⟨((t : ℝ), 0), ⟨t.property, rfl⟩, rfl⟩
  exact (hHr ⟨_, hx⟩).trans (hrval t hx)

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

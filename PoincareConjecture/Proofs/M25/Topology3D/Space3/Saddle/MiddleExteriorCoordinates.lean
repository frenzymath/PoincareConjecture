import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem saddle_middle_exterior_coordinates
    (u : UnitTwoSphere) (c : ℝ)
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (S : Set E3) :
    let L := heightPlaneCoordinates u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let E : ℝ → Set E2 := fun t =>
      {x | L.symm (g x, c + t) ∈ S ∧ 1 ≤ ‖x‖}
    let Ext : ℝ → Set E3 := fun t =>
      L.symm '' ((g '' E t) ×ˢ ({c + t} : Set ℝ))
    (∀ (t : ℝ) (y : E3), y ∈ Ext t ↔
      y ∈ S ∧ H y = c + t ∧
        1 ≤ ‖g.symm (horizontalBandProjection u y)‖) ∧
    (∀ t : ℝ, g '' E t =
      {v : E2 | L.symm (v, c + t) ∈ S} \ (g '' ball (0 : E2) 1)) := by
  intro L H E Ext
  have hpr (t : ℝ) (x : E2) :
      g.symm (horizontalBandProjection u (L.symm (g x, c + t))) = x := by
    simp only [L, horizontalBandProjection_apply,
      ContinuousLinearEquiv.apply_symm_apply, g.symm_apply_apply]
  have hheight (t : ℝ) (x : E2) : H (L.symm (g x, c + t)) = c + t := by
    change ⟪(u : E3), L.symm (g x, c + t)⟫_ℝ = c + t
    rw [← heightPlaneCoordinates_snd u]
    simp only [L, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro t y
    constructor
    · rintro ⟨⟨v, z⟩, ⟨⟨x, hx, rfl⟩, hz⟩, rfl⟩
      have hzt : z = c + t := hz
      subst z
      exact ⟨hx.1, hheight t x, by rw [hpr]; exact hx.2⟩
    · rintro ⟨hy, hh, hn⟩
      let x := g.symm (horizontalBandProjection u y)
      have hrec : L.symm (g x, c + t) = y := by
        dsimp only [x]
        rw [g.apply_symm_apply, horizontalBandProjection_apply]
        exact heightPlaneCoordinates_reconstruct u y (c + t) hh
      refine ⟨(g x, c + t), ⟨⟨x, ?_, rfl⟩, rfl⟩, hrec⟩
      exact ⟨by rwa [hrec], hn⟩
  · intro t
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hx.1, ?_⟩
      rintro ⟨z, hz, hzx⟩
      have heq : z = x := g.injective hzx
      subst z
      exact (not_lt_of_ge hx.2) (mem_ball_zero_iff.mp hz)
    · rintro ⟨hv, hnot⟩
      refine ⟨g.symm v, ⟨?_, ?_⟩, g.apply_symm_apply v⟩
      · simpa only [g.apply_symm_apply, mem_ofPred_eq] using hv
      · apply le_of_not_gt
        intro hn
        exact hnot ⟨g.symm v, mem_ball_zero_iff.mpr hn, g.apply_symm_apply v⟩

theorem saddle_middle_exterior_source_disc
    {A : Type*} (u : UnitTwoSphere) (c t : ℝ)
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (j : A → E3) (V : Set A) (hj : Function.Injective j)
    (hV : ∀ p : A, ⟪(u : E3), j p⟫_ℝ = c + t →
      (horizontalBandProjection u (j p) ∈ g '' ball (0 : E2) 1 ↔ p ∈ V)) :
    let L := heightPlaneCoordinates u
    let E : Set E2 :=
      {x | L.symm (g x, c + t) ∈ range j ∧ 1 ≤ ‖x‖}
    L.symm '' ((g '' E) ×ˢ ({c + t} : Set ℝ)) =
      (range j ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = c + t}) \ (j '' V) := by
  intro L E
  have hmem := (saddle_middle_exterior_coordinates u c g (range j)).1 t
  have hdisc (v : E2) : v ∈ g '' ball (0 : E2) 1 ↔ ‖g.symm v‖ < 1 := by
    rw [mem_image_iff_of_inverse g.symm_apply_apply g.apply_symm_apply,
      mem_ball_zero_iff]
  ext y
  rw [hmem y]
  constructor
  · rintro ⟨⟨p, rfl⟩, hh, hn⟩
    refine ⟨⟨mem_range_self p, hh⟩, ?_⟩
    rintro ⟨q, hq, hqp⟩
    have hp : p ∈ V := by rwa [hj hqp] at hq
    exact (not_lt_of_ge hn) ((hdisc _).mp ((hV p hh).mpr hp))
  · rintro ⟨⟨⟨p, rfl⟩, hh⟩, hnot⟩
    refine ⟨mem_range_self p, hh, le_of_not_gt ?_⟩
    intro hn
    exact hnot ⟨p, (hV p hh).mp ((hdisc _).mpr hn), rfl⟩

theorem saddle_middle_exterior_scaled_source
    {A : Type*} (u : UnitTwoSphere) (c t scale : ℝ) (hscale : scale ≠ 0)
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (j : A → E3) (f : A → ℝ) (r : A → E2)
    (hj : ∀ p : A, j p =
      (heightPlaneCoordinates u).symm (g (r p), c + scale * f p)) :
    let L := heightPlaneCoordinates u
    let E : Set E2 :=
      {x | L.symm (g x, c + t) ∈ range j ∧ 1 ≤ ‖x‖}
    L.symm '' ((g '' E) ×ˢ ({c + t} : Set ℝ)) =
      j '' {p : A | f p = t / scale ∧ 1 ≤ ‖r p‖} := by
  intro L E
  have hmem := (saddle_middle_exterior_coordinates u c g (range j)).1 t
  have hpr (p : A) : g.symm (horizontalBandProjection u (j p)) = r p := by
    rw [hj p]
    simp only [horizontalBandProjection_apply,
      ContinuousLinearEquiv.apply_symm_apply, g.symm_apply_apply]
  have hheight (p : A) : ⟪(u : E3), j p⟫_ℝ = c + scale * f p := by
    rw [hj p, ← heightPlaneCoordinates_snd u,
      ContinuousLinearEquiv.apply_symm_apply]
  ext y
  rw [hmem y]
  constructor
  · rintro ⟨⟨p, rfl⟩, hh, hn⟩
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · have heq : scale * f p = t := by
        change ⟪(u : E3), j p⟫_ℝ = c + t at hh
        rw [hheight p] at hh
        exact add_left_cancel hh
      exact (eq_div_iff hscale).mpr ((mul_comm (f p) scale).trans heq)
    · rwa [hpr p] at hn
  · rintro ⟨p, ⟨hf, hr⟩, rfl⟩
    refine ⟨mem_range_self p, ?_, ?_⟩
    · change ⟪(u : E3), j p⟫_ℝ = c + t
      rw [hheight p, hf, mul_div_cancel₀ t hscale]
    · rwa [hpr p]

end PoincareConjecture.M25.Topology3D

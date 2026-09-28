import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.RetainedCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.ParametrizedCap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.CapTruncation



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

namespace Reverse



theorem exists_parametrized_cap_collar_in_surface
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (C Y : Set E3)
    (hcore : C = liftPlaneDiffeomorph hv b s hs A ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)}))
    (hCY : C ⊆ Y)
    (hcollarY : ∀ q : S1, ∀ t ∈ Icc (-(1 / 4 : Real)) 0,
      (b + s * t) • v + (γ q : E3) ∈ Y) :
    ∃ (g : E2 → E3) (r η : Real),
      ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      1 < r ∧ r < 5 / 4 ∧ r - 1 < η ∧
      g '' closedBall (0 : E2) 1 = C ∧
      g '' closedBall (0 : E2) r ⊆ Y ∧
      ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
        g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3) := by
  obtain ⟨g, hg, hgi, hgd, _, _, ⟨η, hη, _, hcollar⟩, _, hrange⟩ :=
    exists_parametrized_cylindrical_cap_with_range hv γ hγ A hboundary b s hs
  let r := 1 + min η (1 / 4) / 2
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hr : 1 < r := by dsimp [r]; linarith
  have hr' : r < 5 / 4 := by dsimp [r]; linarith [min_le_right η (1 / 4)]
  have hrη : r - 1 < η := by dsimp [r]; linarith [min_le_left η (1 / 4)]
  have hcap : g '' closedBall (0 : E2) 1 = C := hrange.trans hcore.symm
  refine ⟨g, r, η, hg, hgi, hgd, hr, hr', hrη, hcap, ?_, hcollar⟩
  rintro y ⟨x, hx, rfl⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · exact hCY (hcap ▸ mem_image_of_mem g (mem_closedBall_zero_iff.mpr hx1))
  have hxpos : 0 < ‖x‖ := by linarith
  let q : S1 := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ hxpos.ne']⟩
  have hqx : ‖x‖ • (q : E2) = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hxη : |‖x‖ - 1| < η := by
    rw [abs_of_nonneg (by linarith : 0 ≤ ‖x‖ - 1)]
    linarith [mem_closedBall_zero_iff.mp hx]
  rw [← hqx, hcollar q ‖x‖ hxη]
  exact hcollarY q _ (capCollarClock_bounds (by linarith)
    ((mem_closedBall_zero_iff.mp hx).trans hr'.le))

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)



theorem exists_capMinus_collar_in_child :
    ∃ (g : E2 → E3) (r η : Real),
      ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      1 < r ∧ r < 5 / 4 ∧ r - 1 < η ∧
      g '' closedBall (0 : E2) 1 = S.gMinus '' closedBall 0 1 ∧
      g '' closedBall (0 : E2) r ⊆ range S.fMinus ∧
      ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
        g (ρ • (q : E2)) =
          (c - S.a + S.s * Reverse.capCollarClock ρ) • v + (S.γ q : E3) := by
  apply Reverse.exists_parametrized_cap_collar_in_surface S.unit_v (c - S.a) S.s
    S.s_pos.ne' S.γ S.circle_embedding S.A S.circle_image _ _ S.gMinus_range
  · rw [S.fMinus_range]
    exact subset_union_left
  · intro q t ht
    have hlow : -S.ε < -S.a + S.s * t := by
      have hmul := mul_le_mul_of_nonneg_left ht.1 S.s_pos.le
      linarith [S.a_lt_quarter_ε, S.s_lt_eighth_a, S.a_pos]
    have hcut : -S.a + S.s * t ≤ -S.a := by
      have := mul_nonpos_of_nonneg_of_nonpos S.s_pos.le ht.2
      linarith
    refine ⟨S.T (q, -S.a + S.s * t), ?_⟩
    rw [S.retainedMinus_eq _ (S.tube_mem_retainedMinus q hlow hcut),
      S.cylinder q _ ⟨hlow, by linarith [S.a_pos, S.ε_pos]⟩]
    congr 2
    ring


theorem exists_capPlus_collar_in_child :
    ∃ (g : E2 → E3) (r η : Real),
      ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      1 < r ∧ r < 5 / 4 ∧ r - 1 < η ∧
      g '' closedBall (0 : E2) 1 = S.gPlus '' closedBall 0 1 ∧
      g '' closedBall (0 : E2) r ⊆ range S.fPlus ∧
      ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
        g (ρ • (q : E2)) =
          (c + S.a + (-S.s) * Reverse.capCollarClock ρ) • v + (S.γ q : E3) := by
  apply Reverse.exists_parametrized_cap_collar_in_surface S.unit_v (c + S.a) (-S.s)
    (neg_ne_zero.mpr S.s_pos.ne') S.γ S.circle_embedding S.A S.circle_image _ _ S.gPlus_range
  · rw [S.fPlus_range]
    exact subset_union_left
  · intro q t ht
    have hhigh : S.a + (-S.s) * t < S.ε := by
      have hmul := mul_le_mul_of_nonneg_left ht.1 S.s_pos.le
      linarith [S.a_lt_quarter_ε, S.s_lt_eighth_a, S.a_pos]
    have hcut : S.a ≤ S.a + (-S.s) * t := by
      have := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr S.s_pos.le) ht.2
      linarith
    refine ⟨S.T (q, S.a + (-S.s) * t), ?_⟩
    rw [S.retainedPlus_eq _ (S.tube_mem_retainedPlus q hhigh hcut),
      S.cylinder q _ ⟨by linarith [S.a_pos, S.ε_pos], hhigh⟩]
    congr 2
    ring

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

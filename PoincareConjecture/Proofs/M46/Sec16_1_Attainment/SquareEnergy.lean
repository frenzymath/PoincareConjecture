import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.AuxiliaryEnergy
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_MinimizingSequence









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}



theorem backward_squarePath_velocity_clock (p : M14BackwardPath G T 0 tau x y)
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt tau)) :
    (show ℝ from mfderiv (spacetimeModel 3) 𝓘(ℝ) G.spacetime.timeFunction
      (p.curve (s ^ 2))
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) (fun r => p.curve (r ^ 2)) s 1)) =
        -(2 * s) := by
  have ht : s ^ 2 ∈ Ioo 0 tau :=
    ⟨sq_pos_of_pos hs.1, (Real.lt_sqrt hs.1.le).mp hs.2⟩
  have hp := ((p.curve_regular _ ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt
    (by simp)
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (2 * s) • (1 : TangentSpace 𝓘(ℝ, ℝ) (s ^ 2)) := by
    have hv := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ) (s ^ 2) => L 1) hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
      mul_one, one_mul] using hv
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => r ^ 2) (g := p.curve)
    hp hsq.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hsqmf, map_smul, p.derivative_eq _ ht] at hchain
  let dt : TangentSpace (spacetimeModel 3) (p.curve (s ^ 2)) →L[ℝ] ℝ :=
    mfderiv (spacetimeModel 3) 𝓘(ℝ) G.spacetime.timeFunction (p.curve (s ^ 2))
  have hclock : dt (G.spacetime.timeVector (p.curve (s ^ 2))) = 1 :=
    G.spacetime.timeVector_normalized _
  have hhorizontal : dt (p.horizontal_velocity (s ^ 2)).val = 0 :=
    (p.horizontal_velocity (s ^ 2)).property
  change dt (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3)
    (p.curve ∘ fun r => r ^ 2) s 1) = _
  rw [hchain, map_smul, map_add, map_neg, hclock, hhorizontal]
  simp only [smul_eq_mul, add_zero, mul_neg, mul_one]




theorem backward_squarePath_auxiliary_speed (p : M14BackwardPath G T 0 tau x y)
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt tau)) :
    M14.auxiliarySpacetimeForm G.spacetime (p.curve (s ^ 2))
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) (fun r => p.curve (r ^ 2)) s 1)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) (fun r => p.curve (r ^ 2)) s 1) =
        M14.pathSquareKinetic p s + 4 * s ^ 2 := by
  have hproj := M14.squarePath_projectedVelocity p (by simpa only [Real.sqrt_zero] using hs)
  rw [M14.projectedCurveVelocity] at hproj
  rw [M14.auxiliarySpacetimeForm_apply, hproj, backward_squarePath_velocity_clock p hs]
  unfold M14.pathSquareKinetic
  ring




theorem backward_squarePath_edist_le_energy (p : M14BackwardPath G T 0 tau x y)
    {D a b C : ℝ}
    (hkin : IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau))
    (hbound : (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤ D)
    (ha : 0 ≤ a) (hb : b ≤ Real.sqrt tau) (hab : a ≤ b) (hC : 0 < C) :
    M14.auxiliarySpacetimeEDist G.spacetime (p.curve (a ^ 2)) (p.curve (b ^ 2)) ≤
      ENNReal.ofReal ((D + 4 * tau * Real.sqrt tau + (b - a) * C ^ 2) / (2 * C)) := by
  have htau : 0 ≤ tau := p.tau_lt.le
  have hkinNonneg := pathSquareKinetic_nonneg p
  have hclock : IntervalIntegrable (fun s : ℝ => 4 * s ^ 2) volume 0 (Real.sqrt tau) :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hint := hkin.add hclock
  have hsub : Icc a b ⊆ Icc 0 (Real.sqrt tau) := Icc_subset_Icc ha hb
  have hsubo : Ioo a b ⊆ Ioo 0 (Real.sqrt tau) := Ioo_subset_Ioo ha hb
  have hfull : (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s + 4 * s ^ 2) ≤
      D + 4 * tau * Real.sqrt tau := by
    rw [intervalIntegral.integral_add hkin hclock]
    apply add_le_add hbound
    have h := intervalIntegral.integral_mono_on (Real.sqrt_nonneg tau) hclock
      (intervalIntegrable_const (c := 4 * tau)) (fun s hs => by
        have hs2 : s ^ 2 ≤ tau := by
          simpa only [Real.sq_sqrt htau] using
            (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).mpr hs.2
        linarith)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using h
  have hnonneg (s : ℝ) : 0 ≤ M14.pathSquareKinetic p s + 4 * s ^ 2 := by
    exact add_nonneg (hkinNonneg s) (mul_nonneg (by norm_num) (sq_nonneg s))
  have hpart : (∫ s in a..b, M14.pathSquareKinetic p s + 4 * s ^ 2) ≤
      D + 4 * tau * Real.sqrt tau :=
    (intervalIntegral.integral_mono_interval ha hab hb (ae_of_all _ hnonneg) hint).trans hfull
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    rw [M14.auxiliarySpacetimeEDist_self]
    exact bot_le
  · have hcont := (M14.squarePath_continuousOn p).mono
      (show Icc a b ⊆ M14SqrtParameterInterval 0 tau by
        simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hsub)
    have hreg := (M14.squarePath_contMDiffOn p).mono
      (show Ioo a b ⊆ Ioo (Real.sqrt 0) (Real.sqrt tau) by
        simpa only [Real.sqrt_zero] using hsubo)
    have hpartint := hint.mono_set (by rw [uIcc_of_le hab,
      uIcc_of_le (Real.sqrt_nonneg tau)]; exact hsub)
    have h := auxiliary_edist_le_energy_of_interior_regular G.spacetime hlt hC
      hcont hreg hpartint hnonneg (fun s hs =>
        (backward_squarePath_auxiliary_speed p (hsubo hs)).le)
    exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (add_le_add hpart le_rfl) (by positivity)))

end PoincareConjecture.Proofs.M46

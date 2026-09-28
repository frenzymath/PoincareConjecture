import PoincareConjecture.Proofs.M63.Mathlib.NormalizedCoefficients
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.MinimizingGeodesicSide
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem curvature_density_of_parallel_frame (F : RicciFlow n M (Set.Icc a b)) (t : ℝ)
    {gamma : ℝ → M} {X Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s)}
    {f : ℝ → ℝ} {f' x A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hf : HasDerivAt f f' x)
    (hX : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, X s⟩ : TangentBundle (𝓡 n) M)) x)
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) x)
    (hDX : rampHorizontalCovariantDerivative (F.connection t) gamma X x = 0)
    (hDY : rampHorizontalCovariantDerivative (F.connection t) gamma Y x = 0)
    (hvel : ∀ᶠ s in 𝓝 x, curveVelocity (n := n) gamma s = f s • X s + B • Y s)
    (hXX : ∀ᶠ s in 𝓝 x, (F.metric t).inner (gamma s) (X s) (X s) = A ^ 2)
    (hYY : ∀ᶠ s in 𝓝 x, (F.metric t).inner (gamma s) (Y s) (Y s) = 1)
    (hXY : ∀ᶠ s in 𝓝 x, (F.metric t).inner (gamma s) (X s) (Y s) = 0) :
    m62Curvature F (fun s _ => gamma s) t x * curveSpeed F (fun s _ => gamma s) t x =
      A * B * |f'| / (A ^ 2 * f x ^ 2 + B ^ 2) := by
  let v : ℝ → ℝ := fun s => Real.sqrt (A ^ 2 * f s ^ 2 + B ^ 2)
  let u : ℝ → ℝ := fun s => f s / v s
  let w : ℝ → ℝ := fun s => B / v s
  let c1 := B ^ 2 * f' / v x ^ 3
  let c2 := -(A ^ 2 * B * f x * f') / v x ^ 3
  let W := c1 • X x + c2 • Y x
  have hD (s : ℝ) : 0 < A ^ 2 * f s ^ 2 + B ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (f s)))
      (sq_pos_of_pos hB)
  have hv (s : ℝ) : 0 < v s := Real.sqrt_pos.mpr (hD s)
  have hvne : v x ≠ 0 := (hv x).ne'
  have hvsq : v x ^ 2 = A ^ 2 * f x ^ 2 + B ^ 2 := Real.sq_sqrt (hD x).le
  have hu : HasDerivAt u c1 x := hf.div_sqrt_sq_mul_sq_add_sq (A := A) hB.ne'
  have hw : HasDerivAt w c2 x := hf.const_div_sqrt_sq_mul_sq_add_sq (A := A) hB.ne'
  have hspeed : curveSpeed F (fun s _ => gamma s) t =ᶠ[𝓝 x] v := by
    filter_upwards [hvel, hXX, hYY, hXY] with s hs hxx hyy hxy
    have hyx : (F.metric t).inner (gamma s) (Y s) (X s) = 0 :=
      ((F.metric t).symm (gamma s) (Y s) (X s)).trans hxy
    change (F.metric t).tangentNorm (gamma s) (curveVelocity gamma s) = v s
    rw [hs]
    unfold RiemannianMetric.tangentNorm
    congr 1
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hxx, hyy, hxy, hyx]
    ring
  have hS : spatialUnitTangent F (fun s _ => gamma s) t =ᶠ[𝓝 x]
      (fun s => u s • X s + w s • Y s) := by
    filter_upwards [hspeed, hvel] with s hs hh
    change (curveSpeed F (fun s _ => gamma s) t s)⁻¹ • curveVelocity gamma s = _
    rw [hs, hh, smul_add, smul_smul, smul_smul]
    simp only [u, w, div_eq_mul_inv, mul_comm]
  have hweight (c : ℝ → ℝ) (hc : DifferentiableAt ℝ c x)
      (Z : (s : ℝ) → TangentSpace (𝓡 n) (gamma s))
      (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun s => (⟨gamma s, Z s⟩ : TangentBundle (𝓡 n) M)) x) :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun s => (⟨gamma s, c s • Z s⟩ : TangentBundle (𝓡 n) M)) x := by
    rw [mdifferentiableAt_totalSpace] at hZ ⊢
    refine ⟨hZ.1, ?_⟩
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (gamma x)
    have hnear : ∀ᶠ s in 𝓝 x, gamma s ∈ e.baseSet :=
      hZ.1.continuousAt (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
    apply (hc.mdifferentiableAt.smul hZ.2).congr_of_eventuallyEq
    filter_upwards [hnear] with s hs
    change (e ⟨gamma s, c s • Z s⟩).2 = c s • (e ⟨gamma s, Z s⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hs,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hs, map_smul]
  have hSderiv : rampHorizontalCovariantDerivative (F.connection t) gamma
      (spatialUnitTangent F (fun s _ => gamma s) t) x = W := by
    rw [M62.pullback_congr (F.connection t) hS,
      M62.pullback_add (F.connection t) (hweight u hu.differentiableAt X hX)
        (hweight w hw.differentiableAt Y hY),
      M62.pullback_smul (F.connection t) hu hX, M62.pullback_smul (F.connection t) hw hY,
      hDX, hDY, smul_zero, smul_zero, add_zero, add_zero]
  have hyx : (F.metric t).inner (gamma x) (Y x) (X x) = 0 :=
    ((F.metric t).symm (gamma x) (Y x) (X x)).trans hXY.self_of_nhds
  have hinner : (F.metric t).inner (gamma x) W W =
      (A * B * |f'| / (A ^ 2 * f x ^ 2 + B ^ 2)) ^ 2 := by
    calc
      _ = c1 ^ 2 * A ^ 2 + c2 ^ 2 := by
        dsimp only [W]
        simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
          hXX.self_of_nhds, hYY.self_of_nhds, hXY.self_of_nhds, hyx]
        ring
      _ = A ^ 2 * B ^ 2 * f' ^ 2 * (A ^ 2 * f x ^ 2 + B ^ 2) / v x ^ 6 := by
        dsimp only [c1, c2]
        field_simp
        ring
      _ = A ^ 2 * B ^ 2 * f' ^ 2 / v x ^ 4 := by
        rw [← hvsq]
        field_simp
      _ = _ := by
        rw [← hvsq, div_pow, mul_pow, mul_pow, sq_abs]
        ring
  have hq : 0 ≤ A * B * |f'| / (A ^ 2 * f x ^ 2 + B ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg hA hB.le) (abs_nonneg f')) (hD x).le
  have hnorm : (F.metric t).tangentNorm (gamma x) W =
      A * B * |f'| / (A ^ 2 * f x ^ 2 + B ^ 2) := by
    rw [RiemannianMetric.tangentNorm, hinner, Real.sqrt_sq hq]
  have hcurv : m62Curvature F (fun s _ => gamma s) t x =
      (v x)⁻¹ * (F.metric t).tangentNorm (gamma x) W := by
    change (F.metric t).tangentNorm (gamma x)
      ((curveSpeed F (fun s _ => gamma s) t x)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) gamma
          (spatialUnitTangent F (fun s _ => gamma s) t) x) = _
    rw [hspeed.eq_of_nhds, hSderiv, (F.metric t).tangentNorm_smul,
      abs_of_nonneg (inv_nonneg.mpr (hv x).le)]
  rw [hcurv, hspeed.eq_of_nhds, hnorm]
  field_simp

end PoincareConjecture.M63

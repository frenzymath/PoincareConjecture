import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPaths









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

private theorem inverseHorizontal_val (p : G.Point)
    (v : (rescalingTransport hM12 hM13 G Q hQ a).Horizontal p) :
    ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm v).val = v.val := by
  have h := M13.parabolicSpacetimeHorizontal_val G.spacetime Q hQ a p
    ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

private theorem inverseHorizontal_metric (p : G.Point)
    (v w : (rescalingTransport hM12 hM13 G Q hQ a).Horizontal p) :
    G.spacetime.horizontalMetric.inner p
      ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm v)
      ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm w) =
      Q⁻¹ * (rescalingTransport hM12 hM13 G Q hQ a).spacetime.horizontalMetric.inner p v w := by
  have h := M13.parabolicSpacetime_metric G.spacetime Q hQ a p
    ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm v)
    ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).symm w)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  erw [h]
  field_simp



theorem rescalingInverseRawIntegrand
    (γ : ℝ → (rescalingTransport hM12 hM13 G Q hQ a).Point)
    (v : ∀ t, (rescalingTransport hM12 hM13 G Q hQ a).Horizontal (γ t)) (t : ℝ) :
    M14RawLIntegrand G (fun s => γ (Q * s))
      (fun s => Q • (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (γ (Q * s))).symm (v (Q * s))) t =
      Real.sqrt Q * M14RawLIntegrand (rescalingTransport hM12 hM13 G Q hQ a) γ v (Q * t) := by
  unfold M14RawLIntegrand
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [inverseHorizontal_metric hM12 hM13 G Q hQ a,
    rescalingTransport_scalar, Real.sqrt_mul hQ.le]
  field_simp [hQ.ne']
  ring_nf
  rw [Real.sq_sqrt hQ.le]
  ring



noncomputable def rescalingPathInverse
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y) :
    M14BackwardPath G T τ₁ τ₂ x y := by
  have hmap : MapsTo (fun s : ℝ => Q * s) (Icc τ₁ τ₂) (Icc (Q * τ₁) (Q * τ₂)) := by
    intro s hs
    exact ⟨mul_le_mul_of_nonneg_left hs.1 hQ.le, mul_le_mul_of_nonneg_left hs.2 hQ.le⟩
  have hmapo : MapsTo (fun s : ℝ => Q * s) (Ioo τ₁ τ₂) (Ioo (Q * τ₁) (Q * τ₂)) := by
    intro s hs
    exact ⟨mul_lt_mul_of_pos_left hs.1 hQ, mul_lt_mul_of_pos_left hs.2 hQ⟩
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => Q * s) :=
    (contDiff_const.mul contDiff_id).contMDiff
  refine {
    tau_nonneg := (mul_nonneg_iff_of_pos_left hQ).mp p.tau_nonneg
    tau_lt := (mul_lt_mul_iff_right₀ hQ).mp p.tau_lt
    base_time := ?_
    endpoint_time := ?_
    curve := fun s => p.curve (Q * s)
    curve_start := p.curve_start
    curve_end := p.curve_end
    curve_time := ?_
    curve_continuous := p.curve_continuous.comp hc.continuous.continuousOn hmap
    curve_regular := p.curve_regular.comp (hc.of_le (by simp)).contMDiffOn hmapo
    horizontal_velocity := fun s => Q •
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (Q * s))).symm
        (p.horizontal_velocity (Q * s))
    derivative_eq := ?_
    action_integrable := ?_ }
  · have h := p.base_time
    change parabolicTime Q a (G.spacetime.timeFunction x) = parabolicTime Q a T - Q * τ₁ at h
    unfold parabolicTime at h
    nlinarith
  · have h := p.endpoint_time
    change parabolicTime Q a (G.spacetime.timeFunction y) = parabolicTime Q a T - Q * τ₂ at h
    unfold parabolicTime at h
    nlinarith
  · intro s hs
    have h := p.curve_time _ (hmap hs)
    change parabolicTime Q a (G.spacetime.timeFunction (p.curve (Q * s))) =
      parabolicTime Q a T - Q * s at h
    unfold parabolicTime at h
    nlinarith
  · intro s hs
    have hp := (p.curve_regular.contMDiffAt (isOpen_Ioo.mem_nhds (hmapo hs))).mdifferentiableAt
      (by simp)
    have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => Q * r) s
        (ContinuousLinearMap.toSpanSingleton ℝ Q) := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id s).const_mul Q).hasFDerivAt.hasMFDerivAt
    change mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) (p.curve ∘ (fun r => Q * r)) s 1 = _
    rw [mfderiv_comp s hp hd.mdifferentiableAt, hd.mfderiv]
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
    change mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (Q * s) Q = _
    have hscaled : mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (Q * s) Q =
        Q • mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (Q * s) (1 : ℝ) := by
      simpa only [smul_eq_mul, mul_one] using
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (Q * s)).map_smul Q (1 : ℝ)
    rw [hscaled, p.derivative_eq _ (hmapo hs)]
    change Q • (-((1 / Q : ℝ) • G.spacetime.timeVector (p.curve (Q * s))) +
      (p.horizontal_velocity (Q * s)).val) = -G.spacetime.timeVector (p.curve (Q * s)) +
      Q • ((M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (Q * s))).symm (p.horizontal_velocity (Q * s))).val
    rw [inverseHorizontal_val]
    simp only [smul_add, smul_neg, smul_smul, one_div, mul_inv_cancel₀ hQ.ne', one_smul]
  · have h := (p.action_integrable.comp_mul_left (c := Q)).const_mul (Real.sqrt Q)
    have heq : M14RawLIntegrand G (fun s => p.curve (Q * s))
        (fun s => Q • (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
          (p.curve (Q * s))).symm (p.horizontal_velocity (Q * s))) =
        (fun s => Real.sqrt Q * M14RawLIntegrand
          (rescalingTransport hM12 hM13 G Q hQ a) p.curve p.horizontal_velocity (Q * s)) :=
      funext (rescalingInverseRawIntegrand hM12 hM13 G Q hQ a p.curve p.horizontal_velocity)
    rw [heq]
    simpa only [mul_div_cancel_left₀ _ hQ.ne'] using h

private theorem backwardPath_ext {G : GeneralizedLGeometryTransport n X time I}
    {T τ₁ τ₂ : ℝ} {x y : G.Point} {p q : M14BackwardPath G T τ₁ τ₂ x y}
    (hc : p.curve = q.curve)
    (hv : ∀ s, (p.horizontal_velocity s).val = (q.horizontal_velocity s).val) : p = q := by
  cases p
  cases q
  cases hc
  congr 1
  funext s
  exact Subtype.ext (hv s)



theorem rescalingPath_right_inverse
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y) :
    rescalingPath hM12 hM13 G Q hQ a (rescalingPathInverse hM12 hM13 G Q hQ a p) = p := by
  apply backwardPath_ext
  · funext s
    change p.curve (Q * (s / Q)) = p.curve s
    rw [mul_div_cancel₀ _ hQ.ne']
  · intro s
    change ((Q⁻¹ : ℝ) • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
      (p.curve (Q * (s / Q))) (Q •
        (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
          (p.curve (Q * (s / Q)))).symm
            (p.horizontal_velocity (Q * (s / Q))))).val = _
    rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ hQ.ne', one_smul, mul_div_cancel₀ _ hQ.ne']



theorem rescalingPath_minimizing_iff
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14IsMinimizing (rescalingPath hM12 hM13 G Q hQ a p) ↔ M14IsMinimizing p := by
  constructor
  · intro h q
    have hq := h (rescalingPath hM12 hM13 G Q hQ a q)
    rw [rescalingPath_action, rescalingPath_action] at hq
    exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hQ)).mp hq
  · intro h q
    have hq := h (rescalingPathInverse hM12 hM13 G Q hQ a q)
    have heq := rescalingPath_right_inverse hM12 hM13 G Q hQ a q
    rw [← heq, rescalingPath_action, rescalingPath_action]
    exact mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg Q)

end PoincareConjecture.M14

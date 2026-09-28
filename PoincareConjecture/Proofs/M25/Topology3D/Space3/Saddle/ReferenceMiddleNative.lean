import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceAmbientTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology Matrix

namespace PoincareConjecture.M25.Topology3D




theorem saddle_reference_middle_native_tracks
    (u : UnitTwoSphere) (c rho delta a : ℝ)
    (hrho : 0 < rho) (ha : 0 < a)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hplanar : ∀ y : E3, horizontalBandProjection u (F y) =
      g (a • J2.symm (y 0 / Real.sqrt 2, y 1 / Real.sqrt 2)))
    (X : E3 → E3) :
    let L := heightPlaneCoordinates u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let scale := rho ^ 2 * a ^ 2
    let b := 1 / (128 * a ^ 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let Z : Fin 4 → ℝ → ℝ → E3 := fun k h r =>
      !₂[sx k * Real.sqrt (r ^ 2 / a ^ 2 + h),
        sy k * Real.sqrt (r ^ 2 / a ^ 2 - h),
        -Real.sqrt (1 - 2 * r ^ 2 / a ^ 2)]
    let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
      (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
        sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
    let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r =>
      L.symm (g (xi k t r), c + t)
    (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ h : ℝ, |h| ≤ 3 * b → H (F (Z k h r)) = c + scale * h) →
    (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ h : ℝ, |h| ≤ 2 * b →
        HasDerivAt (fun t : ℝ => F (Z k (t / scale) r))
          (X (F (Z k h r))) (scale * h)) →
    (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta → F (Z k (t / scale) r) = Xi k t r) ∧
    (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta →
        HasDerivAt (fun s : ℝ => Xi k s r) (X (Xi k t r)) t) := by
  intro L H scale b sx sy Z xi Xi hWall hNative
  have hscale : 0 < scale := mul_pos (sq_pos_of_pos hrho) (sq_pos_of_pos ha)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hscaleB : scale * (2 * b) = rho ^ 2 / 64 := by
    dsimp only [scale, b]
    field_simp
    ring
  have hwindow (t : ℝ) (ht : |t| < 2 * delta) : |t / scale| ≤ 2 * b := by
    rw [abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).mpr
    rw [mul_comm, hscaleB]
    linarith only [ht, hsmall]
  have hsqrt (v : ℝ) :
      a * Real.sqrt (v / a ^ 2) / Real.sqrt 2 = Real.sqrt (v / 2) := by
    rw [Real.sqrt_div' v (sq_nonneg a), Real.sqrt_sq ha.le,
      mul_div_cancel₀ _ ha.ne', Real.sqrt_div' v (by norm_num : (0 : ℝ) ≤ 2)]
  have hplus (t r : ℝ) :
      r ^ 2 / a ^ 2 + t / scale = (r ^ 2 + t / rho ^ 2) / a ^ 2 := by
    dsimp only [scale]
    field_simp
  have hminus (t r : ℝ) :
      r ^ 2 / a ^ 2 - t / scale = (r ^ 2 - t / rho ^ 2) / a ^ 2 := by
    dsimp only [scale]
    field_simp
  have hvector (k : Fin 4) (t r : ℝ) :
      a • J2.symm ((Z k (t / scale) r) 0 / Real.sqrt 2,
        (Z k (t / scale) r) 1 / Real.sqrt 2) = xi k t r := by
    apply J2.injective
    simp only [map_smul, xi, J2.apply_symm_apply]
    apply Prod.ext
    · change a * (sx k * Real.sqrt (r ^ 2 / a ^ 2 + t / scale) / Real.sqrt 2) = _
      rw [hplus]
      calc
        _ = sx k * (a * Real.sqrt ((r ^ 2 + t / rho ^ 2) / a ^ 2) /
            Real.sqrt 2) := by ring
        _ = _ := by rw [hsqrt]
    · change a * (sy k * Real.sqrt (r ^ 2 / a ^ 2 - t / scale) / Real.sqrt 2) = _
      rw [hminus]
      calc
        _ = sy k * (a * Real.sqrt ((r ^ 2 - t / rho ^ 2) / a ^ 2) /
            Real.sqrt 2) := by ring
        _ = _ := by rw [hsqrt]
  have hpoint (k : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) : F (Z k (t / scale) r) = Xi k t r := by
    apply L.injective
    change L (F (Z k (t / scale) r)) = L (L.symm (g (xi k t r), c + t))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext
    · change horizontalBandProjection u (F (Z k (t / scale) r)) = g (xi k t r)
      rw [hplanar, hvector]
    · have hh := hWall k r hr (t / scale) (by linarith only [hwindow t ht, hb])
      rw [mul_div_cancel₀ _ hscale.ne'] at hh
      exact (heightPlaneCoordinates_snd u _).trans hh
  refine ⟨hpoint, ?_⟩
  intro k r hr t ht
  have hd := hNative k r hr (t / scale) (hwindow t ht)
  rw [mul_div_cancel₀ _ hscale.ne', hpoint k r hr t ht] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2] with s hs
  exact (hpoint k r hr s (abs_lt.mpr hs)).symm

end PoincareConjecture.M25.Topology3D

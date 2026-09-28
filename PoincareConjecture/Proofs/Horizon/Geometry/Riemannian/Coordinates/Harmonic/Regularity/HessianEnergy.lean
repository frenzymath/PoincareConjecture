import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Caccioppoli
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Norm

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integrable_cutoff_hessian_normSq (D : LeviCivitaData g)
    {η f : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x ^ 2 * ∑ i, ∑ j, (D.hessian f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) g.volumeMeasure := by
  apply ((hη.pow 2).continuous.mul
    (D.contMDiff_hessian_normSq hf).continuous).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hηc
  intro x hx
  by_contra hx'
  exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])

variable [PreconnectedSpace M]

theorem harmonic_hessian_energy_le (D : LeviCivitaData g)
    {η f : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hηc : HasCompactSupport η)
    {κ : ℝ} (hharm : ∀ x ∈ tsupport η, D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (hRic : ∀ x ∈ tsupport η,
      -κ * g.inner x (D.gradient f x) (D.gradient f x) ≤
        D.ricci x (D.gradient f x) (D.gradient f x)) :
    (∫ x, η x ^ 2 * ∑ i, ∑ j, (D.hessian f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 ∂g.volumeMeasure) ≤
      2 * κ * (∫ x, η x ^ 2 *
        g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) +
      4 * ∫ x, g.inner x (D.gradient η x) (D.gradient η x) *
        g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let H := fun x => ∑ i, ∑ j, (D.hessian f x
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2
  let t := fun x => g.inner x (D.gradient η x) (D.gradient η x)
  let c := fun x => g.inner x (D.gradient η x) (D.gradient q x)
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q := D.contMDiff_inner_gradient hf hf
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc
    intro x hx
    by_contra hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])
  have hmass : Integrable (fun x => η x ^ 2 * q x) g.volumeMeasure :=
    ((hη.pow 2).continuous.mul hq.continuous).integrable_of_hasCompactSupport hη2c.mul_right
  have hcut : Integrable (fun x => t x * q x) g.volumeMeasure :=
    ((D.continuous_inner_gradient hη hη).mul hq.continuous).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_right
  have hcross := D.integrable_inner_gradient (hη.pow 2) hq hη2c
  have hlap := D.integrable_mul_laplacian (hη.pow 2) hq hη2c
  have hpoint (x : M) : η x ^ 2 * H x ≤
      η x ^ 2 * D.laplacian q x +
        g.inner x (D.gradient (fun y => η y ^ 2) x) (D.gradient q x) +
        2 * κ * (η x ^ 2 * q x) + 4 * (t x * q x) := by
    have hnonneg (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
      by_cases hz : v = 0
      · simp [hz]
      · exact (g.pos x v hz).le
    have hH : 0 ≤ H x :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have ht : 0 ≤ t x := hnonneg _
    have hqx : 0 ≤ q x := hnonneg _
    have hgrad : g.inner x (D.gradient (fun y => η y ^ 2) x) (D.gradient q x) =
        2 * η x * c x := by
      have hηd := (hη x).mdifferentiableAt (by simp)
      have h := D.gradient_mul hηd hηd
      simp only [← pow_two] at h
      rw [h]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      dsimp only [c]
      ring
    rw [hgrad]
    by_cases hx : x ∈ tsupport η
    · have hzero : mvfderiv (𝓡 n) (D.laplacian f) x (D.gradient f x) = 0 := by
        rw [Poincare.mvfderiv_eq_of_eventuallyEq (hharm x hx), mvfderiv_const]
        rfl
      have hb := D.bochner_identity hf x
      rw [hzero] at hb
      change D.laplacian q x = 2 * H x + 2 * 0 + _ at hb
      have hbochner : 2 * (η x ^ 2 * H x) ≤
          η x ^ 2 * D.laplacian q x + 2 * κ * (η x ^ 2 * q x) := by
        have hr := mul_le_mul_of_nonneg_left (hRic x hx) (sq_nonneg (η x))
        have he := congrArg (fun z : ℝ => η x ^ 2 * z) hb
        change η x ^ 2 * (-κ * q x) ≤ _ at hr
        nlinarith only [hr, he]
      have hcs : c x ^ 2 ≤ t x *
          g.inner x (D.gradient q x) (D.gradient q x) := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        have h := real_inner_mul_inner_self_le (D.gradient η x) (D.gradient q x)
        change g.inner x (D.gradient η x) (D.gradient q x) *
            g.inner x (D.gradient η x) (D.gradient q x) ≤
          g.inner x (D.gradient η x) (D.gradient η x) *
            g.inner x (D.gradient q x) (D.gradient q x) at h
        simpa only [c, t, pow_two] using h
      have hkato := D.gradient_normSq_gradient_normSq_le (hf x)
      change g.inner x (D.gradient q x) (D.gradient q x) ≤ 4 * q x * H x at hkato
      have hcs' : c x ^ 2 ≤ 4 * (t x * q x) * H x := by
        have hm := hcs.trans (mul_le_mul_of_nonneg_left hkato ht)
        nlinarith only [hm]
      have hscaled : (-2 * η x * c x) ^ 2 ≤
          4 * (η x ^ 2 * H x) * (4 * (t x * q x)) := by
        have hm := mul_le_mul_of_nonneg_left hcs' (show 0 ≤ 4 * η x ^ 2 by positivity)
        nlinarith only [hm]
      have hsum : 0 ≤ η x ^ 2 * H x + 4 * (t x * q x) := by positivity
      have hyoung : -2 * η x * c x ≤ η x ^ 2 * H x + 4 * (t x * q x) := by
        nlinarith only [hscaled, hsum, sq_nonneg (η x ^ 2 * H x - 4 * (t x * q x))]
      linarith
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by decide : 2 ≠ 0),
        zero_mul, mul_zero, zero_add]
      positivity
  have hint := integral_mono (D.integrable_cutoff_hessian_normSq hη hf hηc)
    (((hlap.add hcross).add (hmass.const_mul (2 * κ))).add (hcut.const_mul 4)) hpoint
  simp only [Pi.add_apply] at hint
  have hadd₁ := integral_add ((hlap.add hcross).add (hmass.const_mul (2 * κ))) (hcut.const_mul 4)
  have hadd₂ := integral_add (hlap.add hcross) (hmass.const_mul (2 * κ))
  have hadd₃ := integral_add hlap hcross
  simp only [Pi.add_apply] at hadd₁ hadd₂ hadd₃
  rw [hadd₁, hadd₂, hadd₃, integral_const_mul, integral_const_mul,
    D.integral_mul_laplacian (hη.pow 2) hq hη2c] at hint
  simpa only [neg_add_cancel, zero_add, H, t, q] using hint

end PoincareConjecture.LeviCivitaData

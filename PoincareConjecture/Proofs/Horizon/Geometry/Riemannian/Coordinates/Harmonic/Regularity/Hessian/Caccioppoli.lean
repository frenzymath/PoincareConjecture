import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Flux
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.PowerEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem hessian_power_inner_nonneg (x : EuclideanSpace ℝ (Fin n))
    (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

private theorem hessian_power_inner_add_le (x : EuclideanSpace ℝ (Fin n))
    (u v : TangentSpace (𝓡 n) x) :
    g.inner x (u + v) (u + v) ≤ 2 * g.inner x u u + 2 * g.inner x v v := by
  have h := hessian_power_inner_nonneg (g := g) x (u - v)
  simp only [map_sub, sub_apply] at h
  simp only [map_add, add_apply]
  rw [g.symm x v u] at h ⊢
  linarith

private theorem hessian_power_weight_sq {w : ℝ} (hw : 0 < w) (p : ℝ) :
    w ^ (2 * p - 2) * w ^ 2 = (w ^ p) ^ 2 := by
  rw [← Real.rpow_mul_natCast hw.le p 2, ← Real.rpow_two, ← Real.rpow_add hw]
  congr 1
  ring

private theorem integrable_hessian_power_derivative_pairing (D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 3}
    {Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z)
    (hZc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v)) :
    Integrable (g.tensorPairingThree F (D.covariantTensorDerivative Z)) g.volumeMeasure := by
  apply (D.contMDiff_tensorPairingThree_derivative hF hZ).continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (D.hasCompactSupport_covariantTensorDerivative hZc)
  intro x hx
  by_contra hx'
  exact hx (by simp [RiemannianMetric.tensorPairingThree, image_eq_zero_of_notMem_tsupport hx'])




theorem regularized_hessian_power_caccioppoli (D : LeviCivitaData g)
    {f η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    {ε p κ L : ℝ} (hε : 0 < ε) (hp : 1 ≤ p) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hharm : ∀ x ∈ tsupport η, D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (hA : ∀ x ∈ tsupport η,
      let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
        fun y v => D.hessian f y (v 0) (v 1);
      -κ * (g.tensorPairingTwo H H x + ε) ≤
        g.tensorPairingTwo (D.twoTensorCurvatureTrace H) H x)
    (hB : ∀ x ∈ tsupport η,
      let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
        fun y v => D.hessian f y (v 0) (v 1)
      g.tensorPairingThree (D.hessianCurvatureFlux f) (D.hessianCurvatureFlux f) x ≤
        L * (g.tensorPairingTwo H H x + ε)) :
    let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
      fun y v => D.hessian f y (v 0) (v 1)
    let w := fun x => Real.sqrt (g.tensorPairingTwo H H x + ε)
    (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
      (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
      22 * p ^ 2 * ((∫ x, (w x ^ p) ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) +
        (κ + L) * ∫ x, η x ^ 2 * (w x ^ p) ^ 2 ∂g.volumeMeasure) := by
  let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
    fun y v => D.hessian f y (v 0) (v 1)
  let A := D.twoTensorCurvatureTrace H
  let B := D.hessianCurvatureFlux f
  let w := fun x => Real.sqrt (g.tensorPairingTwo H H x + ε)
  let Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
    fun x v => (η x ^ 2 * w x ^ (2 * p - 2)) * H x v
  let F := fun x => η x ^ 2 * w x ^ (2 * p - 2) *
    g.inner x (D.gradient w x) (D.gradient w x)
  let G := fun x => (w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)
  let M := fun x => η x ^ 2 * (w x ^ p) ^ 2
  let ST := g.tensorPairingThree (D.covariantTensorDerivative H) (D.covariantTensorDerivative Z)
  let SB := g.tensorPairingThree B (D.covariantTensorDerivative Z)
  let R := g.tensorPairingTwo A Z
  have hfs := contMDiff_iff_contDiff.mpr hf
  have hηs := contMDiff_iff_contDiff.mpr hη
  have hH : IsSmoothCovariantTensor H := D.hessian_isSmoothCovariantTensor hfs
  have hAs : IsSmoothCovariantTensor A := D.twoTensorCurvatureTrace_isSmooth hH
  have hBs : IsSmoothCovariantTensor B := D.hessianCurvatureFlux_isSmooth hfs
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := D.contMDiff_regularized_tensor_norm hH hε
  have hwpos (x : EuclideanSpace ℝ (Fin n)) : 0 < w x :=
    regularized_tensor_norm_pos (g := g) H hε x
  have hw2 (x : EuclideanSpace ℝ (Fin n)) : w x ^ 2 = g.tensorPairingTwo H H x + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos x)).le
  have hwp := contMDiff_rpow_of_pos hw hwpos p
  have hwq := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ := (hηs.pow 2).mul hwq
  have hZ : IsSmoothCovariantTensor Z := hH.scalar_mul hφ
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    rw [show (fun x => η x ^ 2) = η * η by ext x; simp [pow_two]]
    exact hηc.mul_right
  have hZsupport : Function.support
      (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v) ⊆ tsupport η := by
    intro x hx
    by_contra hx'
    apply hx
    ext v
    simp [Z, image_eq_zero_of_notMem_tsupport hx']
  have hZc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v) :=
    HasCompactSupport.of_support_subset_isCompact hηc hZsupport
  have hZη : tsupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v) ⊆ tsupport η :=
    closure_minimal hZsupport (isClosed_tsupport _)
  have hhZ := fun x hx => hharm x (hZη hx)
  have hFi : Integrable F g.volumeMeasure :=
    (hφ.continuous.mul (D.contMDiff_inner_gradient hw hw).continuous).integrable_of_hasCompactSupport
      hη2c.mul_right.mul_right
  have hGi : Integrable G g.volumeMeasure :=
    ((hwp.pow 2).continuous.mul (D.contMDiff_inner_gradient hηs hηs).continuous).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hMi : Integrable M g.volumeMeasure :=
    ((hηs.pow 2).continuous.mul (hwp.pow 2).continuous).integrable_of_hasCompactSupport
      hη2c.mul_right
  have hSTi : Integrable ST g.volumeMeasure :=
    integrable_hessian_power_derivative_pairing D (D.covariantTensorDerivative_isSmooth hH) hZ hZc
  have hSBi : Integrable SB g.volumeMeasure :=
    integrable_hessian_power_derivative_pairing D hBs hZ hZc
  have hRpoint (x) : R x = (η x ^ 2 * w x ^ (2 * p - 2)) * g.tensorPairingTwo A H x := by
    simp only [R, Z, RiemannianMetric.tensorPairingTwo, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hRi : Integrable R g.volumeMeasure := by
    have heq : R = fun x => (η x ^ 2 * w x ^ (2 * p - 2)) * g.tensorPairingTwo A H x :=
      funext hRpoint
    rw [heq]
    exact (hφ.continuous.mul (D.contMDiff_tensorPairingTwo hAs hH).continuous).integrable_of_hasCompactSupport
      hη2c.mul_right.mul_right
  have hGn (x) : 0 ≤ G x := mul_nonneg (sq_nonneg _) (hessian_power_inner_nonneg x _)
  have hMn (x) : 0 ≤ M x := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hG0 : 0 ≤ ∫ x, G x ∂g.volumeMeasure := integral_nonneg hGn
  have hM0 : 0 ≤ ∫ x, M x ∂g.volumeMeasure := integral_nonneg hMn
  have hBweighted (x) : η x ^ 2 * w x ^ (2 * p - 2) * g.tensorPairingThree B B x ≤ L * M x := by
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hB x hx)
        (mul_nonneg (sq_nonneg (η x)) (Real.rpow_nonneg (hwpos x).le (2 * p - 2)))
      change _ ≤ (η x ^ 2 * w x ^ (2 * p - 2)) * (L * (g.tensorPairingTwo H H x + ε)) at h
      rw [← hw2] at h
      have heq := hessian_power_weight_sq (hwpos x) p
      dsimp only [M]
      nlinarith only [h, congrArg (fun z : ℝ => L * η x ^ 2 * z) heq]
    · simp [M, image_eq_zero_of_notMem_tsupport hx]
  have hpoint (x) : (p - 1 / 2) * F x ≤
      ST x - SB x + 5 * G x + ((p + 1) * L) * M x := by
    have h := D.regularized_tensor_power_test_lower hH B hηs hε hp x
    have hb := mul_le_mul_of_nonneg_left (hBweighted x) (show 0 ≤ p + 1 by linarith)
    change (p - 1 / 2) * F x ≤ ST x - SB x + 5 * G x + _ at h
    nlinarith only [h, hb]
  have hi := integral_mono (hFi.const_mul (p - 1 / 2))
    (((hSTi.sub hSBi).add (hGi.const_mul 5)).add (hMi.const_mul ((p + 1) * L))) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  rw [integral_add (f := fun x => ST x - SB x + 5 * G x)
      ((hSTi.sub hSBi).add (hGi.const_mul 5)) (hMi.const_mul ((p + 1) * L)),
    integral_add (f := fun x => ST x - SB x) (hSTi.sub hSBi) (hGi.const_mul 5),
    integral_sub hSTi hSBi,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hweak := D.integral_covariantHessian_pairing hfs hZ hZc hhZ
  change (∫ x, ST x ∂g.volumeMeasure) = (∫ x, SB x ∂g.volumeMeasure) -
    ∫ x, R x ∂g.volumeMeasure at hweak
  have hAlower : -κ * (∫ x, M x ∂g.volumeMeasure) ≤ ∫ x, R x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_mono (hMi.const_mul (-κ)) hRi
    intro x
    rw [hRpoint]
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hA x hx)
        (mul_nonneg (sq_nonneg (η x)) (Real.rpow_nonneg (hwpos x).le (2 * p - 2)))
      change (η x ^ 2 * w x ^ (2 * p - 2)) * (-κ * (g.tensorPairingTwo H H x + ε)) ≤ _ at h
      rw [← hw2] at h
      have heq := hessian_power_weight_sq (hwpos x) p
      dsimp only [M]
      nlinarith only [h, congrArg (fun z : ℝ => κ * η x ^ 2 * z) heq]
    · simp [M, image_eq_zero_of_notMem_tsupport hx]
  have hweighted : (p - 1 / 2) * (∫ x, F x ∂g.volumeMeasure) ≤
      5 * (∫ x, G x ∂g.volumeMeasure) + (κ + (p + 1) * L) *
        ∫ x, M x ∂g.volumeMeasure := by linarith only [hi, hweak, hAlower]
  have hFbound : (∫ x, F x ∂g.volumeMeasure) ≤
      10 * (∫ x, G x ∂g.volumeMeasure) + 4 * (κ + L) *
        ∫ x, M x ∂g.volumeMeasure := by
    apply (mul_le_mul_iff_right₀ (show 0 < p - 1 / 2 by linarith)).mp
    have hkM := mul_nonneg hκ hM0
    have hlM := mul_nonneg hL hM0
    nlinarith only [hweighted, hkM,
      mul_nonneg (sub_nonneg.mpr hp) hG0,
      mul_nonneg (sub_nonneg.mpr hp) hkM,
      mul_nonneg (sub_nonneg.mpr hp) hlM]
  have hcutpoint (x) : g.inner x (D.gradient (fun y => η y * w y ^ p) x)
      (D.gradient (fun y => η y * w y ^ p) x) ≤ 2 * G x + 2 * p ^ 2 * F x := by
    rw [D.gradient_mul ((hηs x).mdifferentiableAt (by simp))
      ((hwp x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos]
    have h := hessian_power_inner_add_le (g := g) x
      (η x • ((p * w x ^ (p - 1)) • D.gradient w x))
      ((w x ^ p) • D.gradient η x)
    have hpow : (w x ^ (p - 1)) ^ 2 = w x ^ (2 * p - 2) := by
      rw [← Real.rpow_mul_natCast (hwpos x).le]
      congr 1
      ring
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    dsimp only [F, G]
    nlinarith only [h, congrArg (fun z : ℝ =>
      2 * η x ^ 2 * p ^ 2 * z * g.inner x (D.gradient w x) (D.gradient w x)) hpow]
  have hcuti := D.integrable_inner_gradient (hηs.mul hwp) (hηs.mul hwp) hηc.mul_right
  have hcut := integral_mono hcuti ((hGi.const_mul 2).add (hFi.const_mul (2 * p ^ 2))) hcutpoint
  simp only [Pi.add_apply] at hcut
  rw [integral_add (hGi.const_mul 2) (hFi.const_mul (2 * p ^ 2)),
    integral_const_mul, integral_const_mul] at hcut
  change (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
    (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
      2 * (∫ x, G x ∂g.volumeMeasure) + 2 * p ^ 2 * ∫ x, F x ∂g.volumeMeasure at hcut
  have hmul := mul_le_mul_of_nonneg_left hFbound (show 0 ≤ 2 * p ^ 2 by positivity)
  have hp2 : 1 ≤ p ^ 2 := by nlinarith only [hp]
  have hKM := mul_nonneg (add_nonneg hκ hL) hM0
  change (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
    (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
    22 * p ^ 2 * ((∫ x, G x ∂g.volumeMeasure) + (κ + L) * ∫ x, M x ∂g.volumeMeasure)
  nlinarith only [hcut, hmul, mul_nonneg (sub_nonneg.mpr hp2) hG0,
    mul_nonneg (sq_nonneg p) hKM]

end PoincareConjecture.LeviCivitaData

import PoincareConjecture.Proofs.M14.Sec6_6_RescalingSquare
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPathInverse









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

include hQ in


theorem rescalingSquareInverseParameter_mapsTo (τ₁ τ₂ : ℝ) :
    MapsTo (fun s : ℝ => Real.sqrt Q * s)
      (M14SqrtParameterInterval τ₁ τ₂) (M14SqrtParameterInterval (Q * τ₁) (Q * τ₂)) := by
  intro s hs
  rw [M14SqrtParameterInterval, Real.sqrt_mul hQ.le, Real.sqrt_mul hQ.le]
  exact ⟨mul_le_mul_of_nonneg_left hs.1 (Real.sqrt_nonneg Q),
    mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg Q)⟩



theorem rescalingSquareInverseCurve_eqOn
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y}
    (R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p) :
    EqOn (fun s => (rescalingPathInverse hM12 hM13 G Q hQ a p).curve (s ^ 2))
      (fun s => R.curve (Real.sqrt Q * s)) (M14SqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  change (rescalingPathInverse hM12 hM13 G Q hQ a p).curve (s ^ 2) =
    R.curve (Real.sqrt Q * s)
  erw [R.agrees _ (rescalingSquareInverseParameter_mapsTo Q hQ τ₁ τ₂ hs)]
  change p.curve (Q * s ^ 2) = p.curve ((Real.sqrt Q * s) ^ 2)
  rw [mul_pow, Real.sq_sqrt hQ.le]



noncomputable def rescalingSquarePathInverse
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y}
    (R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p) :
    M14SquareRootPath G (rescalingPathInverse hM12 hM13 G Q hQ a p) := by
  apply squareRootPathOfSmoothSquare
  have h := (R.smooth.mono R.interval_subset).comp
    (contDiff_const.mul contDiff_id).contMDiff.contMDiffOn
    (rescalingSquareInverseParameter_mapsTo Q hQ τ₁ τ₂)
  exact h.congr (fun _ hs => rescalingSquareInverseCurve_eqOn hM12 hM13 G Q hQ a R hs)



theorem rescalingSquareInverse_initial_velocity
    {T τ : ℝ} {x y : G.Point}
    {p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * 0) (Q * τ) x y}
    (R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p)
    (R' : M14SquareRootPath G (rescalingPathInverse hM12 hM13 G Q hQ a p)) :
    (show SpacetimeModelVector n from (R'.horizontal_velocity 0).val) =
      Real.sqrt Q • (R.horizontal_velocity 0).val := by
  let J := M14SqrtParameterInterval (Q * 0) (Q * τ)
  let K := M14SqrtParameterInterval 0 τ
  have h0 : 0 ∈ J := by simp [J, M14SqrtParameterInterval, Real.sqrt_nonneg]
  have h0' : 0 ∈ K := by simp [K, M14SqrtParameterInterval, Real.sqrt_nonneg]
  have hm : MapsTo (fun s => Real.sqrt Q * s) K J :=
    rescalingSquareInverseParameter_mapsTo Q hQ 0 τ
  have heq : EqOn R'.curve (fun r => R.curve (Real.sqrt Q * r)) K := by
    intro r hr
    exact (R'.agrees r hr).trans (rescalingSquareInverseCurve_eqOn hM12 hM13 G Q hQ a R hr)
  have hτ : 0 < τ := by
    have h := p.tau_lt
    rw [mul_zero] at h
    exact (mul_pos_iff_of_pos_left hQ).mp h
  have hK : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K 0 :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (by norm_num) hτ) 0 h0').uniqueMDiffWithinAt
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => Real.sqrt Q * r) 0
      (ContinuousLinearMap.toSpanSingleton ℝ (Real.sqrt Q)) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt Q)).hasFDerivAt.hasMFDerivAt
  have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (I'' := spacetimeModel n) (f := fun r => Real.sqrt Q * r) (g := R.curve) 0
    (((R.smooth.mono R.interval_subset) _ (hm h0')).mdifferentiableWithinAt (by simp))
    hd.mdifferentiableAt.mdifferentiableWithinAt hm hK
  rw [mfderivWithin_eq_mfderiv hK hd.mdifferentiableAt, hd.mfderiv] at hchain
  have hcongr := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
    (fun r hr => heq hr) h0'
  have hv := congrArg (fun L => L (1 : ℝ)) (hcongr.trans hchain)
  erw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one, mul_zero] at hv
  have hR := R.derivative_eq 0 h0
  have hR' := R'.derivative_eq 0 h0'
  simp only [mul_zero, neg_zero, zero_smul, zero_add] at hR hR'
  dsimp only [J, K] at hv
  simp only [mul_zero] at hv
  erw [hR'] at hv
  have hlin := (mfderivWithin 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve J 0).map_smul
    (Real.sqrt Q) (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hlin
  dsimp only [J] at hlin
  simp only [mul_zero] at hlin
  erw [hlin, hR] at hv
  exact hv

end PoincareConjecture.M14

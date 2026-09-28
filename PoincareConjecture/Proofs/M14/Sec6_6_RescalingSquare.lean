import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPaths
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurvePath









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


theorem rescalingSquareParameter_mapsTo (τ₁ τ₂ : ℝ) :
    MapsTo (fun s : ℝ => s / Real.sqrt Q)
      (M14SqrtParameterInterval (Q * τ₁) (Q * τ₂)) (M14SqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  rw [M14SqrtParameterInterval, Real.sqrt_mul hQ.le, Real.sqrt_mul hQ.le] at hs
  exact ⟨(le_div_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by simpa only [mul_comm] using hs.1),
    (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by simpa only [mul_comm] using hs.2)⟩



theorem rescalingSquareCurve_eqOn
    {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) :
    EqOn (fun s => (rescalingPath hM12 hM13 G Q hQ a p).curve (s ^ 2))
      (fun s => R.curve (s / Real.sqrt Q)) (M14SqrtParameterInterval (Q * τ₁) (Q * τ₂)) := by
  intro s hs
  change (rescalingPath hM12 hM13 G Q hQ a p).curve (s ^ 2) = R.curve (s / Real.sqrt Q)
  erw [R.agrees _ (rescalingSquareParameter_mapsTo Q hQ τ₁ τ₂ hs)]
  change p.curve (s ^ 2 / Q) = p.curve ((s / Real.sqrt Q) ^ 2)
  rw [div_pow, Real.sq_sqrt hQ.le]



noncomputable def rescalingSquarePath
    {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) :
    M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p) := by
  apply squareRootPathOfSmoothSquare
  have h := (R.smooth.mono R.interval_subset).comp
    (contDiff_id.div_const (Real.sqrt Q)).contMDiff.contMDiffOn
    (rescalingSquareParameter_mapsTo Q hQ τ₁ τ₂)
  exact h.congr (fun _ hs => rescalingSquareCurve_eqOn hM12 hM13 G Q hQ a R hs)




theorem rescalingSquare_initial_velocity
    {T τ : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 τ x y}
    (R : M14SquareRootPath G p)
    (R' : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p)) :
    (show SpacetimeModelVector n from (R'.horizontal_velocity 0).val) =
      (Real.sqrt Q)⁻¹ • (R.horizontal_velocity 0).val := by
  let J := M14SqrtParameterInterval 0 τ
  let K := M14SqrtParameterInterval (Q * 0) (Q * τ)
  have h0 : 0 ∈ J := by simp [J, M14SqrtParameterInterval, Real.sqrt_nonneg]
  have h0' : 0 ∈ K := by simp [K, M14SqrtParameterInterval, Real.sqrt_nonneg]
  have hm : MapsTo (fun s => s / Real.sqrt Q) K J :=
    rescalingSquareParameter_mapsTo Q hQ 0 τ
  have heq : EqOn R'.curve (fun r => R.curve (r / Real.sqrt Q)) K := by
    intro r hr
    exact (R'.agrees r hr).trans (rescalingSquareCurve_eqOn hM12 hM13 G Q hQ a R hr)
  have hK : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K 0 :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt
      (mul_nonneg hQ.le p.tau_nonneg)
      (mul_lt_mul_of_pos_left p.tau_lt hQ)) 0 h0').uniqueMDiffWithinAt
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r / Real.sqrt Q) 0
      (ContinuousLinearMap.toSpanSingleton ℝ ((Real.sqrt Q)⁻¹ : ℝ)) := by
    simpa only [id_eq, one_div] using
      ((hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt Q)).hasFDerivAt.hasMFDerivAt
  have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (I'' := spacetimeModel n) (f := fun r => r / Real.sqrt Q) (g := R.curve) 0
    (((R.smooth.mono R.interval_subset) _ (hm h0')).mdifferentiableWithinAt (by simp))
    hd.mdifferentiableAt.mdifferentiableWithinAt hm hK
  rw [mfderivWithin_eq_mfderiv hK hd.mdifferentiableAt, hd.mfderiv] at hchain
  have hcongr := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
    (fun r hr => heq hr) h0'
  have hv := congrArg (fun L => L (1 : ℝ)) (hcongr.trans hchain)
  erw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one, zero_div] at hv
  have hR := R.derivative_eq 0 h0
  have hR' := R'.derivative_eq 0 h0'
  simp only [mul_zero, neg_zero, zero_smul, zero_add] at hR hR'
  dsimp only [K] at hv
  simp only [mul_zero] at hv
  erw [hR'] at hv
  have hlin := (mfderivWithin 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve J 0).map_smul
    ((Real.sqrt Q)⁻¹ : ℝ) (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hlin
  erw [hlin, hR] at hv
  exact hv

end PoincareConjecture.M14

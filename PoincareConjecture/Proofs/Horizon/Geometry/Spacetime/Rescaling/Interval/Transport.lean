import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Interval
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Interval.Smooth
import Mathlib.Analysis.Calculus.Deriv.Mul











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ParabolicRescaling

theorem interval_map_derivative {I J : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (E : SmoothSpacetimeInterval J)
    (f : D.Point → E.Point) (hf : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ f)
    (φ : ℝ → ℝ) (hval : ∀ x, (f x : ℝ) = φ (x : ℝ))
    (x : D.Point) (c : ℝ) (hφ : HasDerivAt φ c (x : ℝ)) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) f x (D.positiveTangent x) =
      c • E.positiveTangent (f x) := by
  let : ChartedSpace (EuclideanHalfSpace 1) D.Point := D.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ D.Point := D.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) E.Point := E.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ E.Point := E.isManifold
  apply (E.inclusionDerivative (f x)).injective
  have houter := mfderiv_comp x
    (E.inclusion_smooth.mdifferentiable (by simp) (f x))
    (hf.mdifferentiable (by simp) x)
  have hscalar := hφ.hasFDerivAt.hasMFDerivAt.comp x
    (D.inclusion_smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hfun : (Subtype.val : E.Point → ℝ) ∘ f =
      φ ∘ (Subtype.val : D.Point → ℝ) := funext hval
  have hderiv := hscalar.mfderiv
  rw [← hfun, houter, ← E.inclusionDerivative_eq,
    ← D.inclusionDerivative_eq] at hderiv
  have hvalue := congrArg
    (fun L : TangentSpace (𝓡∂ 1) x →L[ℝ] ℝ ↦ L (D.positiveTangent x)) hderiv
  change (E.inclusionDerivative (f x))
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) f x (D.positiveTangent x)) =
    (ContinuousLinearMap.toSpanSingleton ℝ c)
      (D.inclusionDerivative x (D.positiveTangent x)) at hvalue
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    SmoothSpacetimeInterval.positiveTangent, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one, map_smul, smul_eq_mul, mul_one] using hvalue

noncomputable def affineIntervalDiffeomorph
    (I : SpacetimeInterval) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (D : SmoothSpacetimeInterval I)
    (E : SmoothSpacetimeInterval (parabolicInterval Q hQ a I)) :
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) D.Point E.Point ∞ where
  toFun := parabolicTimePoint Q hQ a I
  invFun := parabolicTimePointInv Q hQ a I
  left_inv := by
    intro t
    apply Subtype.ext
    exact parabolicTimeInv_parabolicTime Q hQ a t.val
  right_inv := by
    intro s
    apply Subtype.ext
    exact parabolicTime_parabolicTimeInv Q hQ a s.val
  contMDiff_toFun := by
    apply interval_map_smooth D E
    have hclock : ContDiff ℝ ∞ (parabolicTime Q a) :=
      contDiff_const.mul (contDiff_id.sub contDiff_const)
    exact hclock.contMDiff.comp D.inclusion_smooth
  contMDiff_invFun := by
    apply interval_map_smooth E D
    have hclock : ContDiff ℝ ∞ (parabolicTimeInv Q a) :=
      contDiff_const.add (contDiff_id.div_const Q)
    exact hclock.contMDiff.comp E.inclusion_smooth

theorem affineIntervalDiffeomorph_derivative
    (I : SpacetimeInterval) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (D : SmoothSpacetimeInterval I)
    (E : SmoothSpacetimeInterval (parabolicInterval Q hQ a I)) (t : D.Point) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (affineIntervalDiffeomorph I Q hQ a D E) t
      (D.positiveTangent t) =
      Q • E.positiveTangent (affineIntervalDiffeomorph I Q hQ a D E t) := by
  apply interval_map_derivative D E _ (Diffeomorph.contMDiff _) (parabolicTime Q a)
    (fun _ ↦ rfl)
  convert! ((hasDerivAt_id (t : ℝ)).sub_const a).const_mul Q using 1
  simp

theorem affineIntervalDiffeomorph_inverse_derivative
    (I : SpacetimeInterval) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (D : SmoothSpacetimeInterval I)
    (E : SmoothSpacetimeInterval (parabolicInterval Q hQ a I)) (s : E.Point) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (affineIntervalDiffeomorph I Q hQ a D E).symm s
      (E.positiveTangent s) =
      (1 / Q : ℝ) • D.positiveTangent ((affineIntervalDiffeomorph I Q hQ a D E).symm s) := by
  apply interval_map_derivative E D _ (Diffeomorph.contMDiff _) (parabolicTimeInv Q a)
    (fun _ ↦ rfl)
  convert! ((hasDerivAt_id (s : ℝ)).div_const Q).const_add a using 1

noncomputable def parabolicIntervalTransport (T : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : ParabolicIntervalTransport T Q hQ a where
  diffeomorph I := affineIntervalDiffeomorph I Q hQ a
    (T.interval I) (T.interval (parabolicInterval Q hQ a I))
  forward_eq _ _ := rfl
  inverse_eq _ _ := rfl
  derivative I := affineIntervalDiffeomorph_derivative I Q hQ a
    (T.interval I) (T.interval (parabolicInterval Q hQ a I))
  inverse_derivative I := affineIntervalDiffeomorph_inverse_derivative I Q hQ a
    (T.interval I) (T.interval (parabolicInterval Q hQ a I))

end PoincareConjecture.ParabolicRescaling

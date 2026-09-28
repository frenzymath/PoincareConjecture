import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Frame.Transport.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartCurveExtension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Core
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SecondBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Metric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle Topology NNReal RealInnerProductSpace

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem fderiv_bilinear_symm
    {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : A → E →L[ℝ] E →L[ℝ] V) (z : A) (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v) (d : A) (v w : E) :
    fderiv ℝ G z d v w = fderiv ℝ G z d w v := by
  have hfirst := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).clm_apply
    (hasFDerivAt_const w z)
  have hsecond := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const w z)).clm_apply
    (hasFDerivAt_const v z)
  have heq : (fun q ↦ G q v w) =ᶠ[𝓝 z] (fun q ↦ G q w v) :=
    hsym.mono fun _ h ↦ h v w
  have h := (hfirst.congr_of_eventuallyEq heq.symm).unique hsecond
  simpa using congrArg (fun L : A →L[ℝ] V ↦ L d) h

noncomputable def chartConnectionCovector
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ((fderiv ℝ G z (0, v)) w + (fderiv ℝ G z (0, w)) v -
    (((ContinuousLinearMap.apply ℝ ℝ w).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)).comp
        ((fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ ℝ E))))

noncomputable def chartMetricOperator
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (G z)

noncomputable def chartConnection
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
  (z : ℝ × E) (v w : E) : E :=
  Ring.inverse (chartMetricOperator G z)
    ((InnerProductSpace.toDual ℝ E).symm (chartConnectionCovector G z v w))

theorem chartConnectionCovector_apply
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w u : E) :
    chartConnectionCovector G z v w u = (1 / 2 : ℝ) *
      (fderiv ℝ G z (0, v) w u + fderiv ℝ G z (0, w) v u -
        fderiv ℝ G z (0, u) v w) := rfl

theorem chartConnection_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v)
    (v w u : E) :
    G z (chartConnection G z v w) u =
      (1 / 2 : ℝ) * (fderiv ℝ G z (0, v) w u +
        fderiv ℝ G z (0, w) v u - fderiv ℝ G z (0, u) v w) := by
  unfold chartConnection chartMetricOperator
  let A := InnerProductSpace.continuousLinearMapOfBilin (G z)
  let q := (InnerProductSpace.toDual ℝ E).symm (chartConnectionCovector G z v w)
  have hunit : IsUnit A := positive_form_operator_isUnit (G z) hpos
  have hleft := congrArg (fun L : E →L[ℝ] E ↦ L q) (Ring.mul_inverse_cancel A hunit)
  have hleft' : A (Ring.inverse A q) = q := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hleft
  have hpair : ∀ x y : E, inner ℝ (A x) y = G z x y := by
    intro x y
    exact InnerProductSpace.continuousLinearMapOfBilin_apply (G z) x y
  rw [← hpair]
  change inner ℝ (A (Ring.inverse A q)) u = _
  rw [hleft']
  exact InnerProductSpace.toDual_symm_apply

theorem chartConnection_add_left
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (v v' w : E) :
    chartConnection G z (v + v') w =
      chartConnection G z v w + chartConnection G z v' w := by
  have hp : ((0, v + v') : ℝ × E) = (0, v) + (0, v') := by simp
  have hc : chartConnectionCovector G z (v + v') w =
      chartConnectionCovector G z v w + chartConnectionCovector G z v' w := by
    ext u
    simp only [ContinuousLinearMap.add_apply, chartConnectionCovector_apply, hp, map_add]
    ring
  simp only [chartConnection, hc, map_add]

theorem chartConnection_smul_left
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (r : ℝ) (v w : E) :
    chartConnection G z (r • v) w = r • chartConnection G z v w := by
  have hp : ((0, r • v) : ℝ × E) = r • (0, v) := by simp
  have hc : chartConnectionCovector G z (r • v) w =
      r • chartConnectionCovector G z v w := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, chartConnectionCovector_apply, hp, map_smul,
      smul_eq_mul]
    ring
  simp only [chartConnection, hc, map_smul]

theorem chartConnection_add_right
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (v w w' : E) :
    chartConnection G z v (w + w') =
      chartConnection G z v w + chartConnection G z v w' := by
  have hp : ((0, w + w') : ℝ × E) = (0, w) + (0, w') := by simp
  have hc : chartConnectionCovector G z v (w + w') =
      chartConnectionCovector G z v w + chartConnectionCovector G z v w' := by
    ext u
    simp only [ContinuousLinearMap.add_apply, chartConnectionCovector_apply, hp, map_add]
    ring
  simp only [chartConnection, hc, map_add]

theorem chartConnection_smul_right
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E)
    (r : ℝ) (v w : E) :
    chartConnection G z v (r • w) = r • chartConnection G z v w := by
  have hp : ((0, r • w) : ℝ × E) = r • (0, w) := by simp
  have hc : chartConnectionCovector G z v (r • w) =
      r • chartConnectionCovector G z v w := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, chartConnectionCovector_apply, hp, map_smul,
      smul_eq_mul]
    ring
  simp only [chartConnection, hc, map_smul]

noncomputable def chartConnectionBilinear
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E) :
    E →L[ℝ] E →L[ℝ] E :=
  let L : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ (chartConnection G z)
    (chartConnection_add_left G z) (chartConnection_smul_left G z)
    (chartConnection_add_right G z) (fun r v w ↦ chartConnection_smul_right G z r v w)
  ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap.comp
    L).toContinuousLinearMap

@[simp] theorem chartConnectionBilinear_apply
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (z : ℝ × E) (v w : E) :
    chartConnectionBilinear G z v w = chartConnection G z v w := rfl

noncomputable def chartTransportOperator
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
  (z : ℝ × E) (a : E) : E →L[ℝ] E :=
  -chartConnectionBilinear G z a -
    (1 / 2 : ℝ) •
      (Ring.inverse (chartMetricOperator G z)).comp
        ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
          (fderiv ℝ G z (1, 0)))

theorem chartTransportOperator_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v)
    (a v w : E) :
    G z (chartTransportOperator G z a v) w =
      -G z (chartConnection G z a v) w -
        (1 / 2 : ℝ) * fderiv ℝ G z (1, 0) v w := by
  simp only [chartTransportOperator, sub_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_neg, map_smul, smul_eq_mul,
    chartConnectionBilinear_apply]
  let A := chartMetricOperator G z
  let q := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ G z (1, 0) v)
  have hunit : IsUnit A := positive_form_operator_isUnit (G z) hpos
  have hInv := congrArg (fun L : E →L[ℝ] E ↦ L q) (Ring.mul_inverse_cancel A hunit)
  have hpair := InnerProductSpace.continuousLinearMapOfBilin_apply
    (G z) (Ring.inverse A q) w
  have hInv' : A (Ring.inverse A q) = q := by
    simpa [ContinuousLinearMap.mul_apply] using hInv
  have hpair' : inner ℝ (A (Ring.inverse A q)) w =
      G z (Ring.inverse A q) w := by
    change inner ℝ ((InnerProductSpace.continuousLinearMapOfBilin (G z))
      (Ring.inverse A q)) w = G z (Ring.inverse A q) w
    exact hpair
  have hpairG : G z (Ring.inverse A q) w =
      (fderiv ℝ G z (1, 0)) v w := by
    rw [← hpair', hInv']
    exact InnerProductSpace.toDual_symm_apply
  have hpairG' : G z (Ring.inverse (chartMetricOperator G z)
      ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
        ((fderiv ℝ G z (1, 0)) v))) w =
      (fderiv ℝ G z (1, 0)) v w := by
    simpa [A, q] using hpairG
  rw [hpairG']

theorem chartTransportOperator_metric_identity
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (a v w : E) :
    fderiv ℝ G z (1, a) v w +
      G z (chartTransportOperator G z a v) w +
      G z v (chartTransportOperator G z a w) = 0 := by
  have hsplit : ((1 : ℝ), a) = (1, (0 : E)) + (0, a) := by simp
  have hpoint := hsym.self_of_nhds
  rw [hsplit, map_add, add_apply, add_apply,
    hpoint v (chartTransportOperator G z a w),
    chartTransportOperator_pairing G z hpos a v w,
    chartTransportOperator_pairing G z hpos a w v,
    fderiv_bilinear_symm G z hG hsym (1, 0) w v,
    chartConnection_pairing G z hpos a v w,
    chartConnection_pairing G z hpos a w v,
    fderiv_bilinear_symm G z hG hsym (0, a) w v]
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame

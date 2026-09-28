import PoincareConjecture.Proofs.M32.Claim11_35.Components.IntrinsicScalar
import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators InnerProductSpace ENNReal
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.M32

private theorem round_tensorNorm_pullback
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (DH : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w))
    {k : ℕ} {S : CovariantTensorEvaluation 3 M k} {T : CovariantTensorEvaluation 3 N k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hST : ∀ y ∈ U, ∀ v,
      S y v = T (f y) (fun i => mfderiv (𝓡 3) (𝓡 3) f y (v i)))
    (r : ℕ) {x : M} (hx : x ∈ U) :
    g.tensorNorm (D.iteratedCovariantTensorDerivative S r) x =
      h.tensorNorm (DH.iteratedCovariantTensorDerivative T r) (f x) := by
  obtain ⟨e, he⟩ := hinv x hx
  obtain ⟨A, hA⟩ := (DH.iteratedCovariantTensorDerivative_isSmooth hT r).1 (f x)
  apply g.tensorNorm_eq_of_linearEquiv h _ _ x (f x) e.toLinearEquiv
      (fun v w => ?_) (fun v => ?_) A hA
  · change h.inner (f x) (e v) (e w) = g.inner x v w
    have heval (v : TangentSpace (𝓡 3) x) : e v = mfderiv (𝓡 3) (𝓡 3) f x v :=
      congrArg (fun L => L v) he
    simpa only [heval] using (hmetric x hx v w).symm
  · have heval (v : TangentSpace (𝓡 3) x) : e v = mfderiv (𝓡 3) (𝓡 3) f x v :=
      congrArg (fun L => L v) he
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, heval] using
      D.iteratedCovariantTensorDerivative_eq_pullback DH hU hf hinv hmetric hS hT hST r hx v

private def intrinsicScalarTolerance
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (exists_scalar_control_of_covariant_metric_twoJet D p (alpha := 1) (by norm_num)).choose

private theorem intrinsicScalarTolerance_pos
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (p : EuclideanSpace ℝ (Fin 3)) :
    0 < intrinsicScalarTolerance D p :=
  (exists_scalar_control_of_covariant_metric_twoJet D p (by norm_num : (0 : ℝ) < 1)).choose_spec.1

private theorem round_scalar_control_of_local_isometry
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g0 : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D0 : LeviCivitaData g0) (p : EuclideanSpace ℝ (Fin 3))
    {g h : RiemannianMetric 3 M} (D : LeviCivitaData g) (DH : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin 3) → M} {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hp : p ∈ U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : EuclideanSpace ℝ (Fin 3),
      g0.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w))
    (hclose : ∀ r : ℕ, r ≤ 2 → g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) (f p) <
        intrinsicScalarTolerance D0 p) :
    |DH.scalarCurvature (f p) - D0.scalarCurvature p| < 1 := by
  have hB : ContDiffOn ℝ ∞ (h.pullbackCoefficients f) U := by
    intro y hy
    exact (h.contDiffAt_pullbackCoefficients
      (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hpos (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U)
      (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
      0 < h.pullbackCoefficients f y v v := by
    obtain ⟨e, he⟩ := hinv y hy
    apply h.pos
    intro hz
    apply hv
    apply e.injective
    calc
      e v = mfderiv (𝓡 3) (𝓡 3) f y v := congrArg (fun L => L v) he
      _ = 0 := hz
      _ = e 0 := (map_zero e).symm
  obtain ⟨hE, V, hV, hpV, hVU, hEeq⟩ := RiemannianMetric.exists_local_extension
    hU hp (h.pullbackCoefficients f) hB (fun y _ v w => h.symm (f y) _ _) hpos
  let DE := hE.euclideanLeviCivitaData
  have hEmetric (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ V)
      (v w : EuclideanSpace ℝ (Fin 3)) :
      hE.inner y v w = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    change hE.euclideanCoefficients y v w = h.pullbackCoefficients f y v w
    rw [hEeq y hy]
  have hjet (r : ℕ) :
      g0.tensorNorm (D0.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          hE.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) r) p =
      g.tensorNorm (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) (f p) := by
    apply round_tensorNorm_pullback D0 D hV (hf.mono hVU)
      (fun y hy => hinv y (hVU hy)) (fun y hy => hmetric y (hVU hy))
      ((Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor hE).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g0))
      ((Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor h).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g))
      (fun y hy v => ?_) r hpV
    exact congrArg₂ (· - ·) (hEmetric y hy (v 0) (v 1))
      (hmetric y (hVU hy) (v 0) (v 1))
  have hscalar := (exists_scalar_control_of_covariant_metric_twoJet D0 p
    (by norm_num : (0 : ℝ) < 1)).choose_spec.2
      hE DE (fun r hr => (hjet r).trans_lt (hclose r hr))
  have htransport := DE.scalarCurvature_eq_of_local_isometry DH hV
    (hf.mono hVU) hEmetric hpV
  rwa [htransport] at hscalar

private def round_referencePoint : UnitSphere 3 :=
  ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩

private def round_referenceCoefficients (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (16 / (‖x‖ ^ 2 + 4) ^ 2) • innerSL ℝ

private theorem round_referenceCoefficients_smooth : ContDiff ℝ ∞ round_referenceCoefficients := by
  let : IsBoundedSMul ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  have hs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) =>
      16 / (‖x‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun x => by positivity)
  exact hs.smul contDiff_const

private def round_referenceMetric : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients round_referenceCoefficients
    round_referenceCoefficients_smooth
    (fun x v w => by change _ * ⟪v, w⟫_ℝ = _ * ⟪w, v⟫_ℝ; rw [real_inner_comm])
    (fun x v hv => by
      change 0 < (16 / (‖x‖ ^ 2 + 4) ^ 2) * ⟪v, v⟫_ℝ
      exact mul_pos (by positivity) (real_inner_self_pos.mpr hv))

private theorem round_referenceMetric_pullback (q : UnitSphere 3)
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    round_referenceMetric.inner x v w = (roundSphereMetric 3).inner
      ((chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x)
      (mfderiv (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x v)
      (mfderiv (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x w) :=
  (roundSphereMetric_chart_symm_inner q x v w).symm

private theorem round_referenceMetric_scalar :
    round_referenceMetric.leviCivitaData.scalarCurvature 0 = 6 := by
  have he := round_referenceMetric.leviCivitaData.scalarCurvature_eq_of_local_isometry
    (roundSphereMetric 3).leviCivitaData isOpen_univ
    (sphere_chart_symm_contMDiff round_referencePoint).contMDiffOn
    (fun x _ v w => round_referenceMetric_pullback round_referencePoint x v w)
    (mem_univ (0 : EuclideanSpace ℝ (Fin 3)))
  rw [he]
  have hs := (roundSphereMetric 3).leviCivitaData.scalarCurvature_of_constant_sectional
    ((chartAt (EuclideanSpace ℝ (Fin 3)) round_referencePoint).symm 0) 1
    (roundSphereMetric_unit_sectionalCurvature _)
  norm_num at hs
  exact hs

private def round_componentTolerance : ℝ :=
  intrinsicScalarTolerance round_referenceMetric.leviCivitaData 0

private theorem round_scalar_close_of_unit_curvature
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (D : LeviCivitaData g) (DH : LeviCivitaData h)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1)
    (x : M)
    (hclose : ∀ r : ℕ, r ≤ 2 → g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) x < round_componentTolerance) :
    |DH.scalarCurvature x - 6| < 1 := by
  have hsec' (y : M) (v w : TangentSpace (𝓡 3) y)
      (hn : g.inner y v v * g.inner y w w - (g.inner y v w) ^ 2 ≠ 0) :
      D.sectionalCurvature y v w = 1 :=
    D.sectionalCurvature_eq_of_orthonormal y 1
      (fun a b haa hbb hab => hsec y a b ⟨haa, hbb, hab⟩) v w hn
  obtain ⟨F, hq, hFx, hF, _, hFm⟩ := SpaceForm.exists_local_isometry_of_unit_curvature
    (roundSphereMetric 3) g (roundSphereMetric 3).leviCivitaData D
    roundSphereMetric_unit_sectionalCurvature hsec' round_referencePoint x
  let c := chartAt (EuclideanSpace ℝ (Fin 3)) round_referencePoint
  let f := F ∘ c.symm
  let U : Set (EuclideanSpace ℝ (Fin 3)) := c.symm ⁻¹' F.source
  have hU : IsOpen U := F.open_source.preimage
    (sphere_chart_symm_contMDiff round_referencePoint).continuous
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U := by
    simpa only [U, mem_preimage, c, sphere_chart_symm_zero] using hq
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    hF.comp (sphere_chart_symm_contMDiff round_referencePoint).contMDiffOn (fun _ hy => hy)
  have hfm (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U)
      (v w : EuclideanSpace ℝ (Fin 3)) :
      round_referenceMetric.inner y v w = g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    have hder := mfderiv_comp y
      ((hF.contMDiffAt (F.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
      ((sphere_chart_symm_contMDiff round_referencePoint y).mdifferentiableAt (by simp))
    change _ = g.inner (F (c.symm y))
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y v)
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y w)
    rw [hder]
    exact (round_referenceMetric_pullback round_referencePoint y v w).trans (hFm _ hy _ _)
  have hinv (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    have hb := round_referenceMetric.mfderiv_bijective_of_pullback_eq g y
      (fun v w => (hfm y hy v w).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : EuclideanSpace ℝ (Fin 3) → Type _) _
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f y)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) _
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) f y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  have hfzero : f 0 = x := by
    simpa only [f, Function.comp_apply, c, sphere_chart_symm_zero] using hFx
  have he := round_scalar_control_of_local_isometry round_referenceMetric.leviCivitaData 0
    D DH hU hzero hf hinv hfm
    (fun r hr => by simpa only [hfzero, round_componentTolerance] using hclose r hr)
  simpa only [hfzero, round_referenceMetric_scalar] using he

private theorem round_forward_mfderiv_injective
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) : Function.Injective (mfderiv (𝓡 3) (𝓡 3) N.forward x) := by
  have hopen : IsOpen N.carrier := N.forward_image ▸ N.forward_openEmbedding.isOpen_range
  have hx : N.forward x ∈ N.carrier := N.forward_image ▸ mem_range_self x
  have hi := N.inverse_smooth.contMDiffAt (hopen.mem_nhds hx)
  have hchain := mfderiv_comp x (hi.mdifferentiableAt (by simp))
    ((N.forward_smooth x).mdifferentiableAt (by simp))
  have heq : N.inverse ∘ N.forward = id := funext N.left_inverse
  rw [heq, mfderiv_id] at hchain
  intro v w hvw
  have h := congrArg (fun z => mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x) z) hvw
  change ((mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)).comp
    (mfderiv (𝓡 3) (𝓡 3) N.forward x)) v =
    ((mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)).comp
      (mfderiv (𝓡 3) (𝓡 3) N.forward x)) w at h
  rw [← hchain] at h
  exact h

private def round_normalizedMetric
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon) :
    RiemannianMetric 3 N.model.carrier :=
  RiemannianMetric.Induced.pullbackMetric (rescaledMetric g N.scale N.scale_pos)
    N.forward N.forward_smooth (round_forward_mfderiv_injective N)

private theorem round_normalizedMetric_scalar
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (x : N.model.carrier) :
    (round_normalizedMetric N).leviCivitaData.scalarCurvature x =
      N.scale⁻¹ * D.scalarCurvature (N.forward x) := by
  have h := (round_normalizedMetric N).leviCivitaData.scalarCurvature_eq_of_local_isometry
    (rescaledMetric_connection g D N.scale N.scale_pos) isOpen_univ
    N.forward_smooth.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
  simpa only [rescaledMetric_scalarCurvature] using h

private theorem round_metric_error_norm_lt
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    {r : ℕ} (hr : r ≤ ⌊epsilon⁻¹⌋₊) (x : N.model.carrier) :
    N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          (round_normalizedMetric N).inner y (v 0) (v 1) -
            N.model_metric.inner y (v 0) (v 1)) r) x < epsilon := by
  obtain ⟨b, hb, hbound⟩ := N.metric_comparison
  have hterm := Finset.single_le_sum
    (s := Finset.range (⌊epsilon⁻¹⌋₊ + 1)) (a := r)
    (f := fun j => (N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative
        (fun y v => N.scale * singularMetricPullback g N.forward y v -
          N.model_metric.inner y (v 0) (v 1)) j) x) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hs := hterm.trans_lt ((hbound x).trans_lt hb)
  change (N.model_metric.tensorNorm
    (N.model_connection.iteratedCovariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        (round_normalizedMetric N).inner y (v 0) (v 1) -
        N.model_metric.inner y (v 0) (v 1)) r) x) ^ 2 < epsilon ^ 2 at hs
  nlinarith [N.epsilon_pos]

private theorem round_normalized_scalar_close
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (hepsilon : epsilon ≤ min round_componentTolerance (1 / 200))
    (x : N.model.carrier) :
    |N.scale⁻¹ * D.scalarCurvature (N.forward x) - 6| < 1 := by
  let : CompactSpace N.model.carrier := isCompact_univ_iff.mp N.model_compact
  have htwo : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply (Nat.le_floor_iff (inv_nonneg.mpr N.epsilon_pos.le)).mpr
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    have he := hepsilon.trans (min_le_right _ _)
    norm_num
    linarith
  have h := round_scalar_close_of_unit_curvature N.model_connection
    (round_normalizedMetric N).leviCivitaData N.model_curvature_one x (fun r hr =>
      (round_metric_error_norm_lt N (hr.trans htwo) x).trans_le
        (hepsilon.trans (min_le_left _ _)))
  rwa [round_normalizedMetric_scalar N D x] at h

private theorem round_normalized_inner_le
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (hepsilon : epsilon ≤ 1 / 200) (x : N.model.carrier)
    (v : TangentSpace (𝓡 3) x) :
    (round_normalizedMetric N).inner x v v ≤ 2 * N.model_metric.inner x v v := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
    ⟨N.model_metric.toRiemannianMetric⟩
  let T : CovariantTensorEvaluation 3 N.model.carrier 2 := fun y w =>
    (round_normalizedMetric N).inner y (w 0) (w 1) -
      N.model_metric.inner y (w 0) (w 1)
  have hT : IsSmoothCovariantTensor T :=
    (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor
      (round_normalizedMetric N)).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.model_metric)
  obtain ⟨A, hA⟩ := hT.1 x
  have heval := abs_tensor_evaluation_le_tensorNorm N.model_metric T x A hA ![v, v]
  have hn : 0 ≤ N.model_metric.inner x v v := by
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  have hnorm : N.model_metric.tensorNorm T x ≤ 1 :=
    (round_metric_error_norm_lt N (Nat.zero_le _) x).le.trans (by linarith)
  have heval' : |(round_normalizedMetric N).inner x v v - N.model_metric.inner x v v| ≤
      N.model_metric.tensorNorm T x * N.model_metric.inner x v v := by
    simpa only [T, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      RiemannianMetric.tangentNorm, ← pow_two, Real.sq_sqrt hn] using heval
  have hmul := mul_le_mul_of_nonneg_right hnorm hn
  linarith [le_abs_self ((round_normalizedMetric N).inner x v v -
    N.model_metric.inner x v v)]

private theorem round_model_edist_le
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (x y : N.model.carrier) :
    N.model_metric.edist x y ≤ ENNReal.ofReal (Real.sqrt 15) := by
  let : CompactSpace N.model.carrier := isCompact_univ_iff.mp N.model_compact
  let : ConnectedSpace N.model.carrier := connectedSpace_iff_univ.mpr N.model_connected
  have hcomplete : MetricComplete N.model_metric := by
    let : RiemannianBundle (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
      ⟨N.model_metric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
      ⟨⟨N.model_metric.inner, N.model_metric.toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace N.model.carrier :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) N.model.carrier
    change CompleteSpace N.model.carrier
    infer_instance
  have hRic (z : N.model.carrier) (v : TangentSpace (𝓡 3) z) :
      2 * N.model_metric.inner z v v ≤ N.model_connection.ricci z v v := by
    have heq := N.model_connection.ricci_of_constant_sectional z 1
      (N.model_connection.sectionalCurvature_eq_of_orthonormal z 1
        (fun a b haa hbb hab => N.model_curvature_one z a b ⟨haa, hbb, hab⟩)) v v
    norm_num at heq
    exact heq.ge
  have hd := N.model_metric.edist_le_of_positive_ricci N.model_connection hcomplete
    (by norm_num : (0 : ℝ) < 2) hRic x y
  norm_num at hd
  exact hd

private theorem round_scaled_edist_le
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (hepsilon : epsilon ≤ 1 / 200) {Q : ℝ} (hQ : 0 < Q)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    (rescaledMetric g Q hQ).edist x y ≤
      ENNReal.ofReal (2 * Real.sqrt (Q / N.scale) * Real.sqrt 15) := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
    ⟨N.model_metric.toRiemannianMetric⟩
  have hratio := div_pos hQ N.scale_pos
  have hfactor : 0 < 2 * Real.sqrt (Q / N.scale) := by positivity
  have hbound (z : N.model.carrier) (v : TangentSpace (𝓡 3) z) :
      (rescaledMetric g Q hQ).inner (N.forward z)
        (mfderiv (𝓡 3) (𝓡 3) N.forward z v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward z v) ≤
      (2 * Real.sqrt (Q / N.scale)) ^ 2 * N.model_metric.inner z v v := by
    have h := round_normalized_inner_le N hepsilon z v
    have hn : 0 ≤ N.model_metric.inner z v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    have hsquare : (2 * Real.sqrt (Q / N.scale)) ^ 2 = 4 * (Q / N.scale) := by
      rw [mul_pow, Real.sq_sqrt hratio.le]
      norm_num
    rw [hsquare]
    have hmul := mul_le_mul_of_nonneg_left h hratio.le
    have hidentity : (Q / N.scale) * (round_normalizedMetric N).inner z v v =
        (rescaledMetric g Q hQ).inner (N.forward z)
          (mfderiv (𝓡 3) (𝓡 3) N.forward z v)
          (mfderiv (𝓡 3) (𝓡 3) N.forward z v) := by
      change (Q / N.scale) * (N.scale * _) = Q * _
      field_simp [N.scale_pos.ne']
      rfl
    rw [hidentity] at hmul
    nlinarith [mul_nonneg hratio.le hn]
  have hd := N.model_metric.edist_le_mul_of_inner_mfderiv_le
    (rescaledMetric g Q hQ) (N.forward_smooth.of_le (by simp)) hfactor hbound
    (N.inverse x) (N.inverse y)
  rw [N.right_inverse hx, N.right_inverse hy] at hd
  exact hd.trans ((mul_le_mul_right (round_model_edist_le N _ _) _).trans_eq
    (ENNReal.ofReal_mul hfactor.le).symm)

private theorem round_radius_estimate {q m : ℝ} (hq : 0 < q) (hm : 0 < m)
    (hqm : m * q < 7) :
    2 * Real.sqrt q * Real.sqrt 15 < 32 * m ^ (-1 / 2 : ℝ) := by
  have hsq : (2 * Real.sqrt q * Real.sqrt 15 * Real.sqrt m) ^ 2 = 60 * (m * q) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hq.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hm.le]
    ring
  have hlt : 2 * Real.sqrt q * Real.sqrt 15 * Real.sqrt m < 32 := by
    nlinarith
  apply (mul_lt_mul_iff_left₀ (Real.sqrt_pos.mpr hm)).mp
  apply hlt.trans_eq
  have hinv : m ^ (-1 / 2 : ℝ) * Real.sqrt m = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hm]
    norm_num
  rw [mul_assoc, hinv, mul_one]

theorem exists_round_component_normalized_bounds :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
        {epsilon : ℝ} (N : SingularRoundComponent g epsilon),
        epsilon ≤ epsilon0 →
        (∀ x ∈ N.carrier, |N.scale⁻¹ * D.scalarCurvature x - 6| < 1) ∧
          ∀ {Q m : ℝ} (hQ : 0 < Q), 0 < m → ∀ {o : M}, o ∈ N.carrier →
            m ≤ D.scalarCurvature o / Q →
            N.carrier ⊆ (rescaledMetric g Q hQ).ball o (32 * m ^ (-1 / 2 : ℝ)) := by
  refine ⟨min round_componentTolerance (1 / 200),
    lt_min (intrinsicScalarTolerance_pos _ _) (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ g D epsilon N hepsilon
  have hscalar (x : M) (hx : x ∈ N.carrier) :
      |N.scale⁻¹ * D.scalarCurvature x - 6| < 1 := by
    simpa only [N.right_inverse hx] using
      round_normalized_scalar_close N D hepsilon (N.inverse x)
  refine ⟨hscalar, ?_⟩
  intro Q m hQ hm o ho hnormalized y hy
  have hupper : D.scalarCurvature o < 7 * N.scale := by
    apply (div_lt_iff₀ N.scale_pos).mp
    have h := (abs_lt.mp (hscalar o ho)).2
    rw [div_eq_mul_inv]
    nlinarith only [h]
  have hscale : m * (Q / N.scale) < 7 := by
    rw [← mul_div_assoc, div_lt_iff₀ N.scale_pos]
    exact ((le_div_iff₀ hQ).mp hnormalized).trans_lt hupper
  change (rescaledMetric g Q hQ).edist o y < ENNReal.ofReal _
  exact (round_scaled_edist_le N (hepsilon.trans (min_le_right _ _)) hQ ho hy).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (round_radius_estimate (div_pos hQ N.scale_pos) hm hscale))

end PoincareConjecture.M32

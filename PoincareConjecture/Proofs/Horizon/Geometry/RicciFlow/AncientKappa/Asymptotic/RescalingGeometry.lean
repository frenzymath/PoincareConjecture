import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

private theorem metric_eq_of_inner_eq (g h : RiemannianMetric n M)
    (heq : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = h.inner x v w) :
    g = h := by
  have hi : g.inner = h.inner := by
    funext x
    exact ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ heq x v w
  cases g
  cases h
  cases hi
  rfl

namespace AncientRescaling

variable {K : AncientKappaSolution n M} {tau : ℝ} (R : AncientRescaling K tau)

theorem metric_eq_rescaledMetric (t : ℝ) (ht : t < 0) :
    R.flow.metric t = rescaledMetric (K.flow.metric (tau * t)) (1 / tau)
      (one_div_pos.mpr R.tau_pos) := by
  apply metric_eq_of_inner_eq
  intro x v w
  exact R.metric_scale t ht x v w

theorem complete (t : ℝ) (ht : t < 0) : MetricComplete (R.flow.metric t) := by
  rw [R.metric_eq_rescaledMetric t ht]
  exact metricComplete_rescaledMetric _ _ _
    (K.complete (tau * t) (mul_nonpos_of_nonneg_of_nonpos R.tau_pos.le ht.le))

theorem edist_scale (t : ℝ) (ht : t < 0) (x y : M) :
    (R.flow.metric t).edist x y =
      ENNReal.ofReal (Real.sqrt (1 / tau)) * (K.flow.metric (tau * t)).edist x y := by
  rw [R.metric_eq_rescaledMetric t ht, rescaledMetric_edist]

theorem ball_scale (t : ℝ) (ht : t < 0) (p : M) (r : ℝ) :
    (R.flow.metric t).ball p (Real.sqrt (1 / tau) * r) =
      (K.flow.metric (tau * t)).ball p r := by
  ext x
  change (R.flow.metric t).edist p x < ENNReal.ofReal (Real.sqrt (1 / tau) * r) ↔ _
  rw [R.edist_scale t ht, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (one_div_pos.mpr R.tau_pos)))
    ENNReal.ofReal_ne_top

end AncientRescaling

private theorem calibratedMetricVolume_rescaledMetric
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c) :
    calibratedMetricVolume (rescaledMetric g c hc) =
      ENNReal.ofReal (Real.sqrt c) ^ n • calibratedMetricVolume g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₁ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let H₁ := @Measure.hausdorffMeasure M m₁ inferInstance inferInstance (n : ℝ)
  let g' := rescaledMetric g c hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₂ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let H₂ := @Measure.hausdorffMeasure M m₂ inferInstance inferInstance (n : ℝ)
  let C : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  have hCeq : (C : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hCne : C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hne : (C : ℝ≥0∞) ≠ 0 := by
    rw [hCeq]
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  have hLip : @LipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C id := by
    intro x y
    change g'.edist x y ≤ (C : ℝ≥0∞) * g.edist x y
    rw [rescaledMetric_edist, ← hCeq]
  have hAnti : @AntilipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C⁻¹ id := by
    intro x y
    change g.edist x y ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * g'.edist x y
    rw [rescaledMetric_edist, ENNReal.coe_inv hCne, ← hCeq]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]
  have hH : H₂ = (C : ℝ≥0∞) ^ n • H₁ := by
    ext s hs
    have hup : H₂ s ≤ (C : ℝ≥0∞) ^ n * H₁ s := by
      simpa only [Set.image_id, ENNReal.rpow_natCast] using
        (@LipschitzWith.hausdorffMeasure_image_le M M m₁ m₂
          inferInstance inferInstance inferInstance inferInstance (K := C) (f := id)
          hLip (d := (n : ℝ)) (by positivity) s)
    have hlo : H₁ s ≤ ((C : ℝ≥0∞) ^ n)⁻¹ * H₂ s := by
      simpa only [Set.image_id, ENNReal.rpow_natCast,
        ENNReal.coe_inv hCne, ENNReal.inv_pow] using
        (@AntilipschitzWith.le_hausdorffMeasure_image M M m₁ m₂
          inferInstance inferInstance inferInstance inferInstance (K := C⁻¹) (f := id)
          (d := (n : ℝ)) hAnti (by positivity) s)
    have hmul : (C : ℝ≥0∞) ^ n * H₁ s ≤
        (C : ℝ≥0∞) ^ n * (((C : ℝ≥0∞) ^ n)⁻¹ * H₂ s) := by
      gcongr
    rw [← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ hne)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top), one_mul] at hmul
    exact le_antisymm hup hmul
  change _ • H₂ = ENNReal.ofReal (Real.sqrt c) ^ n • (_ • H₁)
  rw [hH, hCeq, smul_comm]

namespace AncientRescaling

variable {K : AncientKappaSolution n M} {tau : ℝ} (R : AncientRescaling K tau)

theorem volume_scale (t : ℝ) (ht : t < 0) (E : Set M) :
    calibratedMetricVolume (R.flow.metric t) E =
      ENNReal.ofReal (Real.sqrt (1 / tau)) ^ n *
        calibratedMetricVolume (K.flow.metric (tau * t)) E := by
  rw [R.metric_eq_rescaledMetric t ht, calibratedMetricVolume_rescaledMetric,
    Measure.smul_apply, smul_eq_mul]

theorem noncollapsed (t : ℝ) (ht : t < 0) (p : M) (r : ℝ) (hr : 0 < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (R.flow.metric t).ball p r,
      |(R.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (K.kappa * r ^ n) ≤
      calibratedMetricVolume (R.flow.metric t) ((R.flow.metric t).ball p r) := by
  let q := Real.sqrt (1 / tau)
  have hq : 0 < q := Real.sqrt_pos.mpr (one_div_pos.mpr R.tau_pos)
  have hq2 : q ^ 2 = 1 / tau := Real.sq_sqrt (one_div_pos.mpr R.tau_pos).le
  have hr' : 0 < r / q := div_pos hr hq
  have ht' : tau * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos R.tau_pos.le ht.le
  have hrad : (r / q) ^ 2 = tau * r ^ 2 := by
    rw [div_pow, hq2]
    field_simp
  have hball : (K.flow.metric (tau * t)).ball p (r / q) =
      (R.flow.metric t).ball p r := by
    simpa only [q, mul_div_cancel₀ r hq.ne'] using
      (R.ball_scale t ht p (r / q)).symm
  have hcurv' : ∀ s ∈ Ioc (tau * t - (r / q) ^ 2) (tau * t),
      ∀ x ∈ (K.flow.metric (tau * t)).ball p (r / q),
        |(K.flow.connection s).curvatureTensorNorm x| ≤ (r / q)⁻¹ ^ 2 := by
    intro s hs x hx
    have htime : s / tau ∈ Ioc (t - r ^ 2) t := by
      rw [hrad] at hs
      constructor
      · apply (lt_div_iff₀ R.tau_pos).mpr
        nlinarith [hs.1]
      · apply (div_le_iff₀ R.tau_pos).mpr
        nlinarith [hs.2]
    have h := hcurv (s / tau) htime x (hball ▸ hx)
    rw [R.curvature_norm_scale _ (lt_of_le_of_lt htime.2 ht),
      mul_div_cancel₀ _ R.tau_pos.ne', abs_mul, abs_of_pos R.tau_pos] at h
    have hradius : (r / q)⁻¹ ^ 2 = r⁻¹ ^ 2 / tau := by
      rw [inv_div, div_pow, hq2]
      simp only [div_eq_mul_inv, inv_pow]
      ring
    rw [hradius]
    exact (le_div_iff₀ R.tau_pos).mpr (by simpa only [mul_comm] using h)
  have hvol := K.noncollapsed (r / q) hr' (tau * t) ht' p (r / q) hr' le_rfl hcurv'
  have hscale : q ^ n * (K.kappa * (r / q) ^ n) = K.kappa * r ^ n := by
    rw [div_pow]
    field_simp
  rw [R.volume_scale t ht, ← hball]
  calc
    ENNReal.ofReal (K.kappa * r ^ n) =
        ENNReal.ofReal q ^ n * ENNReal.ofReal (K.kappa * (r / q) ^ n) := by
      rw [← ENNReal.ofReal_pow hq.le, ← ENNReal.ofReal_mul (pow_nonneg hq.le n), hscale]
    _ ≤ _ := by gcongr

theorem nonnegative_curvature_operator (t : ℝ) (ht : t < 0) (x : M) :
    (R.flow.connection t).NonnegativeCurvatureOperator x := by
  let g := K.flow.metric (tau * t)
  let D := K.flow.connection (tau * t)
  let c := 1 / tau
  have hc : 0 < c := one_div_pos.mpr R.tau_pos
  let D' := rescaledMetric_connection g D c hc
  have hcurv (a b v w : TangentSpace (𝓡 n) x) :
      (R.flow.connection t).curvatureTensor x a b v w =
        c * D.curvatureTensor x a b v w := by
    calc
      _ = D'.curvatureTensor x a b v w :=
        (R.flow.connection t).curvatureTensor_eq_of_inner_eq_nhds D'
          (Filter.Eventually.of_forall (fun y u v ↦ R.metric_scale t ht y u v)) a b v w
      _ = _ := rescaledMetric_curvatureTensor g D c hc x a b v w
  intro A hA
  let b := (R.flow.metric t).orthonormalBasis x
  have hsource := D.curvatureOperator_nonneg_in_frame x
    (K.nonnegative_curvature_operator (tau * t)
      (mul_nonpos_of_nonneg_of_nonpos R.tau_pos.le ht.le) x) b A hA
  have hquad : (R.flow.connection t).curvatureOperatorQuadratic x A =
      c * ∑ i, ∑ j, ∑ k, ∑ l,
        A i j * A k l * D.curvatureTensor x (b i) (b j) (b k) (b l) := by
    unfold LeviCivitaData.curvatureOperatorQuadratic
    simp only [hcurv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [b]
    ring
  rw [hquad]
  exact mul_nonneg hc.le hsource

end AncientRescaling

end PoincareConjecture

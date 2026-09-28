import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricFormTest
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTimePotential
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.RawTestOperator
import PoincareConjecture.Proofs.M03.Existence.DeTurckHigherDomainNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff Manifold

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

open EuclideanDerivativeNative DeTurckHigherDomainNative

theorem vectorTestValue_inner_integral (K : Set V)
    (f h : Fin m → supportedTests K) :
    inner ℝ (vectorTestValue K f) (vectorTestValue K h) =
      ∫ x, ∑ j, (f j : 𝓢(V, ℝ)) x * (h j : 𝓢(V, ℝ)) x := by
  rw [PiLp.inner_apply]
  have hi (j : Fin m) :
      Integrable (fun x => (f j : 𝓢(V, ℝ)) x * (h j : 𝓢(V, ℝ)) x) :=
    (schwartzProduct (f j : 𝓢(V, ℝ)) (h j : 𝓢(V, ℝ))).integrable
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  exact EuclideanDerivativeNative.inner_schwartzToLp (f j : 𝓢(V, ℝ)) (h j : 𝓢(V, ℝ))

private theorem supported_entropy_source_cutoff {K : Set V}
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : V → ℝ) (hηK : ∀ x ∈ K, η x = 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (f : Fin n → supportedTests K) (x : V) :
    η x * g.pullbackVolumeDensity id x *
        fieldEntropySource D (schwartzField (fun j => (f j : 𝓢(V, ℝ))))
          (normBoundEntropy Q) x =
      g.pullbackVolumeDensity id x *
        fieldEntropySource D (schwartzField (fun j => (f j : 𝓢(V, ℝ))))
          (normBoundEntropy Q) x := by
  by_cases hx : x ∈ K
  · rw [hηK x hx, one_mul]
  · have hz : schwartzField (fun j => (f j : 𝓢(V, ℝ))) x = 0 := by
      rw [schwartzField_apply]
      apply PiLp.ext
      exact fun j => (f j).property x hx
    simp only [fieldEntropySource, fieldNormSq, hz, map_zero, mul_zero,
      normBoundEntropy_zero_of_le hQ, sub_self]

private theorem raw_smooth_entropy_pointwise {K : Set V} (hK : IsCompact K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (f : Fin n → supportedTests K) (x : V) :
    (∑ j, (metricEntropySupportedTests hK g η η.smooth' Q f j : 𝓢(V, ℝ)) x *
      (vectorTestGenerator hK.isClosed (rawCutoffPrincipalCoefficient g η hη)
        (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f j : 𝓢(V, ℝ)) x) +
      metricEntropyTimePotential D η Q
        (x, schwartzField (fun j => (f j : 𝓢(V, ℝ))) x) =
      g.pullbackVolumeDensity id x *
        fieldEntropySource D (schwartzField (fun j => (f j : 𝓢(V, ℝ))))
          (normBoundEntropy Q) x := by
  let X : 𝓢(V, V) := schwartzField (fun j => (f j : 𝓢(V, ℝ)))
  have hZ (j : Fin n) :
      (metricEntropySupportedTests hK g η η.smooth' Q f j : 𝓢(V, ℝ)) x =
        metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, X x) := rfl
  have hL (j : Fin n) := raw_vectorTestGenerator_geometric hK.isClosed D η hη hηK f x j
  simp only [hZ, hL]
  change (∑ j, metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, X x) *
    (@Add.add V inferInstance (fieldTraceHessian D X x)
      (RicciFlow.ricciSharp D x (X x))) j) + _ = _
  rw [metricEntropy_operator_cancellation]
  exact supported_entropy_source_cutoff D η hηK hQ f x

private theorem raw_smooth_entropy_integral_nonpos {K : Set V} (hK : IsCompact K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hR : ∀ x, 0 ≤ D.scalarCurvature x)
    (f : Fin n → supportedTests K) :
    (∫ x, ∑ j, (metricEntropySupportedTests hK g η η.smooth' Q f j : 𝓢(V, ℝ)) x *
      (vectorTestGenerator hK.isClosed (rawCutoffPrincipalCoefficient g η hη)
        (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f j : 𝓢(V, ℝ)) x) +
      (∫ x, metricEntropyTimePotential D η Q
        (x, schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)) ≤ 0 := by
  let X : 𝓢(V, V) := schwartzField (fun j => (f j : 𝓢(V, ℝ)))
  let Z := metricEntropySupportedTests hK g η η.smooth' Q f
  let L := vectorTestGenerator hK.isClosed (rawCutoffPrincipalCoefficient g η hη)
    (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f
  have he (x : V) : (∑ j, (Z j : 𝓢(V, ℝ)) x * (L j : 𝓢(V, ℝ)) x) +
      metricEntropyTimePotential D η Q (x, X x) =
      g.pullbackVolumeDensity id x * fieldEntropySource D X (normBoundEntropy Q) x :=
    raw_smooth_entropy_pointwise hK D η hη hηK hQ f x
  have hiP : Integrable (fun x => ∑ j, (Z j : 𝓢(V, ℝ)) x * (L j : 𝓢(V, ℝ)) x) :=
    integrable_finsetSum _ fun j _ =>
      (schwartzProduct (Z j : 𝓢(V, ℝ)) (L j : 𝓢(V, ℝ))).integrable
  have hXc : HasCompactSupport X := schwartzField_hasCompactSupport hK f
  have hφ0 : normBoundEntropy Q 0 = 0 := normBoundEntropy_zero_of_le hQ
  have hiS : Integrable (fun x =>
      g.pullbackVolumeDensity id x * fieldEntropySource D X (normBoundEntropy Q) x) := by
    have hc := (raw_volumeDensity_contDiff g).continuous.mul
      (fieldEntropySource_contDiff D X.smooth' (normBoundEntropy_contDiff Q)).continuous
    exact hc.integrable_of_hasCompactSupport
      (fieldEntropySource_hasCompactSupport D hXc hφ0).mul_left
  have hiT : Integrable (fun x => metricEntropyTimePotential D η Q (x, X x)) := by
    apply (hiS.sub hiP).congr
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      exact sub_eq_iff_eq_add.mpr ((he x).symm.trans (add_comm _ _))
  have hsource := integral_fieldEntropySource_nonpos D X.smooth' (normBoundEntropy_contDiff Q)
    hXc hφ0 (normBoundEntropy_nonneg Q) (normBoundEntropy_deriv_nonneg Q)
    (normBoundEntropy_second_nonneg Q) hR
  change (∫ x, ∑ j, (Z j : 𝓢(V, ℝ)) x * (L j : 𝓢(V, ℝ)) x) +
    (∫ x, metricEntropyTimePotential D η Q (x, X x)) ≤ 0
  rw [← integral_add hiP hiT]
  simpa only [he] using! hsource

theorem raw_smooth_form_entropy_nonpos {K : Set V} (hK : IsCompact K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hR : ∀ x, 0 ≤ D.scalarCurvature x)
    (f : Fin n → supportedTests K) :
    inner ℝ (finiteHilbertMap (dirichletInclusion K)
        (vectorTestForm K (metricEntropySupportedTests hK g η η.smooth' Q f)))
        (rawLowerFormOperator D hK.isClosed η hη (vectorTestForm K f)) -
      principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη)
        (vectorTestForm K (metricEntropySupportedTests hK g η η.smooth' Q f))
        (vectorTestForm K f) +
      (∫ x, metricEntropyTimePotential D η Q
        (x, schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)) ≤ 0 := by
  let Z := metricEntropySupportedTests hK g η η.smooth' Q f
  let L := vectorTestGenerator hK.isClosed (rawCutoffPrincipalCoefficient g η hη)
    (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f
  have hpair := vectorTestGenerator_compatibility hK.isClosed
    (rawCutoffPrincipalCoefficient g η hη) (rawCutoffFirstComponent D η hη)
    (rawCutoffZeroComponent D η hη) f (vectorTestForm K Z)
  change inner ℝ (vectorTestValue K Z) (vectorTestValue K L) = _ at hpair
  have hval := vectorTestValue_inner_integral K Z L
  have hpair' := hval.symm.trans hpair
  have hresult := raw_smooth_entropy_integral_nonpos hK D η hη hηK hQ hR f
  change (∫ x, ∑ j, (Z j : 𝓢(V, ℝ)) x * (L j : 𝓢(V, ℝ)) x) + _ ≤ 0 at hresult
  rw [hpair'] at hresult
  exact hresult

end PoincareConjecture.M35.Uniqueness.Heat

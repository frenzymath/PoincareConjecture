import PoincareConjecture.Proofs.M03.Existence.DeTurckResidualNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckStateApproximationNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorBoundsNative
import PoincareConjecture.Proofs.M03.Existence.MetricPerturbationNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckPositiveStateNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckResidualNative
  DeTurckStateApproximationNative SpectralHeatNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)

local notation "StateD" => State d.SymmetricIndex

def emptyProbeCoefficients (k : ℕ) :
    NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) k →L[ℝ]
      C(M, Coefficients (Fin d.fieldCount)) := by
  let e : (d.ProbeIndex → ℝ) →L[ℝ] Coefficients (Fin d.fieldCount) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d.ProbeIndex => ℝ)).symm.toContinuousLinearMap
  let atEmpty : (WordIndex (Fin d.fieldCount) k → C(M, ℝ)) →L[ℝ] C(M, ℝ) :=
    ContinuousLinearMap.proj (wordIndex ([] : List (Fin d.fieldCount)) (by simp))
  let atProbe (ab : d.ProbeIndex) :
      NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) k →L[ℝ]
        (WordIndex (Fin d.fieldCount) k → C(M, ℝ)) :=
    ContinuousLinearMap.proj ab
  exact (e.compLeftContinuous ℝ M).comp
      ((packContinuous (M := M) (A := d.ProbeIndex)).comp
        (ContinuousLinearMap.pi (fun ab => atEmpty.comp (atProbe ab))))

theorem emptyProbeCoefficients_apply (k : ℕ)
    (Q : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) k)
    (x : M) (ab : d.ProbeIndex) :
    emptyProbeCoefficients d k Q x ab = Q ab (wordIndex [] (by simp)) x := by
  change packContinuous
    (fun cd : d.ProbeIndex => Q cd (wordIndex ([] : List (Fin d.fieldCount)) (by simp))) x ab = _
  exact packContinuous_apply _ x ab

def traceCoefficients (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    StateD →L[ℝ] C(M, Coefficients (Fin d.fieldCount)) :=
  (emptyProbeCoefficients d (r + 1)).comp (lowInput d L r p hpr hp)

theorem traceCoefficients_apply (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : StateD) (x : M) (ab : d.ProbeIndex) :
    traceCoefficients d L r p hpr hp z x ab =
      lowInput d L r p hpr hp z ab (wordIndex [] (by simp)) x :=
  emptyProbeCoefficients_apply d (r + 1) _ x ab

theorem traceCoefficients_smoothTensorCoordinates (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) (x : M) :
    traceCoefficients d L r p hpr hp (d.smoothTensorCoordinates (2 * r + 1) h hsymm) x =
      probes d.fields h x := by
  ext ab
  rw [traceCoefficients_apply]
  exact lowInput_smoothTensorCoordinates d L r p hpr hp h hsymm ab [] (by simp) x

def positivityRadius (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) : ℝ :=
  1 / (4 * (‖traceCoefficients d L r p hpr hp‖ + 1))

theorem positivityRadius_pos (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) : 0 < positivityRadius d L r p hpr hp := by
  unfold positivityRadius
  positivity

theorem traceCoefficients_norm_le_quarter (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : StateD)
    (hz : ‖z‖ ≤ positivityRadius d L r p hpr hp) (x : M) :
    ‖traceCoefficients d L r p hpr hp z x‖ ≤ 1 / 4 := by
  have hden : 0 < 4 * (‖traceCoefficients d L r p hpr hp‖ + 1) := by positivity
  have hsmall := (le_div_iff₀ hden).mp hz
  have hbound := ((traceCoefficients d L r p hpr hp z).norm_coe_le_norm x).trans
    ((traceCoefficients d L r p hpr hp).le_opNorm z)
  nlinarith [norm_nonneg z]

private theorem metric_diagonal_nonneg (x : M) (v : TangentSpace (𝓡 n) x) :
    0 ≤ g0.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g0.pos x v hv).le

theorem smoothTensor_quarter_bound (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤
      positivityRadius d L r p hpr hp) (x : M) (v : TangentSpace (𝓡 n) x) :
    |h x v v| ≤ (1 / 4 : ℝ) * g0.inner x v v := by
  let z := d.smoothTensorCoordinates (2 * r + 1) h hsymm
  calc
    |h x v v| = |nativeDecode g0 d.fields x (traceCoefficients d L r p hpr hp z x) v v| := by
      rw [traceCoefficients_smoothTensorCoordinates, nativeDecode_probes g0 d.fields d.parseval]
    _ ≤ ‖traceCoefficients d L r p hpr hp z x‖ * g0.inner x v v :=
      nativeDecode_diagonal_bound g0 d.fields d.parseval x _ v
    _ ≤ (1 / 4 : ℝ) * g0.inner x v v :=
      mul_le_mul_of_nonneg_right (traceCoefficients_norm_le_quarter d L r p hpr hp z hsmall x)
        (metric_diagonal_nonneg x v)

def smallMetricPerturbation (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤
      positivityRadius d L r p hpr hp) : SmallMetricPerturbation g0 where
  tensor := h
  symm := hsymm
  small := fun x v => (smoothTensor_quarter_bound d L r p hpr hp h hsymm hsmall x v).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      (metric_diagonal_nonneg x v))
  smooth := h.contMDiff

theorem smallMetricPerturbation_metric_inner (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤
      positivityRadius d L r p hpr hp) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (smallMetricPerturbation d L r p hpr hp h hsymm hsmall).metric.inner x v w =
      g0.inner x v w + h x v w := rfl

theorem smallMetricPerturbation_lower_bound (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤
      positivityRadius d L r p hpr hp) (x : M) (v : TangentSpace (𝓡 n) x) :
    (3 / 4 : ℝ) * g0.inner x v v ≤
      (smallMetricPerturbation d L r p hpr hp h hsymm hsmall).metric.inner x v v := by
  have hneg := neg_le_of_abs_le (smoothTensor_quarter_bound d L r p hpr hp h hsymm hsmall x v)
  rw [smallMetricPerturbation_metric_inner]
  linarith

theorem exists_positive_smooth_approximation (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) {rho : ℝ} (hrho : 0 < rho)
    (hpositive : rho ≤ positivityRadius d L r p hpr hp) (z : StateD)
    (hz : ‖shiftedBaseMultiplier d.symmetricParameters z‖ < rho) :
    ∃ h : ℕ → SmoothTensor (n := n) (M := M),
      ∃ hs : ∀ j (x : M) (v w : TangentSpace (𝓡 n) x), h j x v w = h j x w v,
      ∃ g : ℕ → RiemannianMetric n M,
        Tendsto (fun j => d.smoothTensorCoordinates (2 * r + 2) (h j) (hs j)) atTop (𝓝 z) ∧
        (∀ j, ‖d.smoothTensorCoordinates (2 * r + 1) (h j) (hs j)‖ < rho) ∧
        (∀ j (x : M) (v w : TangentSpace (𝓡 n) x),
          (g j).inner x v w = g0.inner x v w + h j x v w) ∧
        ∀ j (x : M) (v : TangentSpace (𝓡 n) x),
          (3 / 4 : ℝ) * g0.inner x v v ≤ (g j).inner x v v := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L (r + 1) z
  have hhigh : Tendsto (fun j => d.smoothTensorCoordinates (2 * r + 2) (h j) (hs j))
      atTop (𝓝 z) := by simpa only [Nat.mul_add, Nat.mul_one] using hlim
  have hJ (j : ℕ) : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) (h j) (hs j)) =
        d.smoothTensorCoordinates (2 * r + 1) (h j) (hs j) := by
    simpa only [Nat.add_assoc] using
      shiftedBase_smoothTensorCoordinates d (2 * r + 1) (h j) (hs j)
  have htrace : Tendsto (fun j => d.smoothTensorCoordinates (2 * r + 1) (h j) (hs j))
      atTop (𝓝 (shiftedBaseMultiplier d.symmetricParameters z)) := by
    simpa only [Function.comp_def, hJ] using
      ((shiftedBaseMultiplier d.symmetricParameters).continuous.tendsto z).comp hhigh
  have hevent : ∀ᶠ j in atTop,
      ‖d.smoothTensorCoordinates (2 * r + 1) (h j) (hs j)‖ < rho :=
    htrace.norm (Iio_mem_nhds hz)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hsmall (j : ℕ) : ‖d.smoothTensorCoordinates (2 * r + 1) (h (j + N)) (hs (j + N))‖ < rho :=
    hN (j + N) (by omega)
  let g (j : ℕ) : RiemannianMetric n M :=
    (smallMetricPerturbation d L r p hpr hp (h (j + N)) (hs (j + N))
      ((hsmall j).le.trans hpositive)).metric
  refine ⟨fun j => h (j + N), fun j => hs (j + N), g,
    hhigh.comp (tendsto_add_atTop_nat N), hsmall, ?_, ?_⟩
  · intro j x v w
    exact smallMetricPerturbation_metric_inner d L r p hpr hp _ _ _ x v w
  · intro j x v
    exact smallMetricPerturbation_lower_bound d L r p hpr hp _ _ _ x v

end PoincareConjecture.DeTurckPositiveStateNative

end

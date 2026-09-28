import PoincareConjecture.Proofs.M03.Existence.DeTurckIntegralPDENative
import PoincareConjecture.Proofs.M03.Existence.DeTurckSmoothMetricFamilyNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckFamilyRecoveryNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckResponseMetricNative

open TensorProbeNative TensorHilbertNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckParameterForcingNative
  DeTurckPullbackForcingNative DeTurckSpatialRecoveryNative
  DeTurckPositiveStateNative DeTurckIntegralPDENative
  DeTurckSmoothMetricFamilyNative SpectralHeatNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (r p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))

structure Response where
  parameters : NativeParameterData d r
  radius_le : parameters.radius ≤ positivityRadius d L r p hpr hp
  T : ℝ
  time_pos : 0 < T
  time_le_one : T ≤ 1
  forcing : ForcingSpace d.SymmetricIndex T
  fixed : parameters.spatialResidual.forcingResidual time_pos.le forcing = forcing
  forcing_small : ‖forcing‖ ≤ parameters.spatialResidual.forcingRadius / 3
  spatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(Icc (0 : ℝ) T, ℝ)) ∞
      (probePath d L r p (by omega) hp
        (responsePath time_pos.le d.symmetricParameters forcing) ab)

theorem exists_response : Nonempty (Response d L r p hpr hp) := by
  obtain ⟨A⟩ := exists_compatibleChartCover (n := n) (M := M)
  obtain ⟨K, hK⟩ := exists_nativeParameterData d L A r p hpr hp
    (positivityRadius_pos d L r p hpr hp)
  obtain ⟨T, hT, hT1, F, hfix, hsmall, horbits⟩ :=
    exists_fixedPoint_with_smooth_orbits d K L (P := Fin n → ℝ) p hpr hp hK
  refine ⟨⟨K, hK, T, hT, hT1, F, hfix, hsmall, ?_⟩⟩
  intro ab
  refine contMDiff_probePath_of_parameter_orbits d L r p (by omega) hp
    (responsePath hT.le d.symmetricParameters F) ?_ ab
  intro U hU h0 Phi hPhi0 hPhi hInv
  obtain ⟨orbit, hsmooth, _, C, hC, V, hV, h0V, _, hdom, heq⟩ :=
    horbits U hU h0 Phi hPhi0 hPhi hInv
  exact ⟨V, hV.mem_nhds h0V, C, hC, hdom, orbit, hsmooth, heq⟩

namespace Response

variable {d L r p hpr hp} (R : Response d L r p hpr hp)

def path : C(Icc (0 : ℝ) R.T, State d.SymmetricIndex) :=
  responsePath R.time_pos.le d.symmetricParameters R.forcing

theorem forcing_twice_le_radius : 2 * ‖R.forcing‖ ≤ R.parameters.radius := by
  have hR := R.parameters.forcingRadius_lt
  have hpos := R.parameters.spatialResidual.forcingRadius_pos
  have hsmall := R.forcing_small
  linarith

theorem trace_small (t : Icc (0 : ℝ) R.T) :
    ‖d.smoothTensorCoordinates (2 * r + 1)
      (recoveredTensor d L r p (by omega) hp R.path R.spatial t)
      (recoveredTensor_symmetric d L r p (by omega) hp R.path R.spatial t)‖ ≤
        positivityRadius d L r p hpr hp := by
  exact (recoveredTensor_traceCoordinates_norm_le d L r p (by omega) hp
    R.time_pos.le R.forcing R.spatial R.time_le_one t).trans
      (R.forcing_twice_le_radius.trans R.radius_le)

def metric (t : ℝ) : RiemannianMetric n M :=
  recoveredMetric d L r p hpr hp R.path R.spatial R.trace_small
    (projIcc 0 R.T R.time_pos.le t)

theorem metric_inner (t : Icc (0 : ℝ) R.T) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (R.metric t).inner x v w = g0.inner x v w +
      recoveredTensor d L r p (by omega) hp R.path R.spatial t x v w := by
  unfold metric
  rw [projIcc_of_mem R.time_pos.le t.property]
  rfl

theorem metric_lower_bound (t : ℝ) (x : M) (v : TangentSpace (𝓡 n) x) :
    (3 / 4 : ℝ) * g0.inner x v v ≤ (R.metric t).inner x v v :=
  recoveredMetric_lower_bound d L r p hpr hp R.path R.spatial R.trace_small
    (projIcc 0 R.T R.time_pos.le t) x v

theorem metric_initial : R.metric 0 = g0 := by
  unfold metric
  apply recoveredMetric_eq_initial
  rw [projIcc_of_mem R.time_pos.le (show (0 : ℝ) ∈ Icc 0 R.T from
    ⟨le_rfl, R.time_pos.le⟩)]
  exact responseState_zero d.symmetricParameters R.forcing

theorem metric_equation_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) R.T)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (R.metric s).inner x v w)
      (MetricFamilyProducerNative.deTurckRHS g0 (R.metric t) x v w)
      (Icc (0 : ℝ) R.T) t := by
  have hd := recoveredMetric_hasDerivWithinAt d L r p (by omega) hp R.time_pos.le
    R.forcing R.spatial R.parameters R.time_le_one R.fixed
    R.forcing_twice_le_radius R.metric R.metric_inner ht
    (MetricFamilyProducerNative.connection (R.metric t))
    (MetricFamilyProducerNative.connection g0) x v w
  have hfield : MetricFamilyProducerNative.deTurckField g0 (R.metric t) =
      DeTurckNative.intrinsicDeTurckField (MetricFamilyProducerNative.connection (R.metric t))
        (MetricFamilyProducerNative.connection g0) := by
    funext y
    rfl
  simpa only [DeTurckNative.smoothRicciDeTurckTensor_apply,
    MetricFamilyProducerNative.deTurckRHS, MetricFamilyProducerNative.lieTerm,
    hfield] using hd

theorem metric_equation {t : ℝ} (ht : t ∈ Ico (0 : ℝ) R.T)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (R.metric s).inner x v w)
      (MetricFamilyProducerNative.deTurckRHS g0 (R.metric t) x v w)
      (Ico (0 : ℝ) R.T) t :=
  (R.metric_equation_Icc (Ico_subset_Icc_self ht) x v w).mono Ico_subset_Icc_self

theorem tensor_integral_equation (t : Icc (0 : ℝ) R.T) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    recoveredTensor d L r p (by omega) hp R.path R.spatial t x v w =
      ∫ s in (0 : ℝ)..t,
        DeTurckNative.smoothRicciDeTurckTensor
          (MetricFamilyProducerNative.connection (R.metric (projIcc 0 R.T R.time_pos.le s)))
          (MetricFamilyProducerNative.connection g0) x v w :=
  recoveredTensor_integral_equation d L r p (by omega) hp R.time_pos.le
    R.forcing R.spatial R.parameters R.time_le_one R.fixed
    R.forcing_twice_le_radius R.metric R.metric_inner
    (fun t => MetricFamilyProducerNative.connection (R.metric t))
    (MetricFamilyProducerNative.connection g0) t x v w

theorem metric_smooth_Icc : RiemannianMetric.IsSmoothFamilyOn R.metric (Icc 0 R.T) := by
  apply recoveredMetric_isSmoothFamilyOn d L R.time_pos r p hpr hp R.path
    R.spatial R.trace_small R.metric
  · intro t x v w
    unfold metric
    rw [projIcc_of_mem R.time_pos.le t.property]
  · intro t ht x v w
    exact R.metric_equation_Icc ht x v w

theorem metric_smooth : RiemannianMetric.IsSmoothFamilyOn R.metric (Ico 0 R.T) :=
  R.metric_smooth_Icc.mono (prod_mono Ico_subset_Icc_self subset_rfl)

def nativeFamily : NativeDeTurckFamily g0 where
  T := R.T
  hT := R.time_pos
  metric := R.metric
  initial := R.metric_initial
  smooth := R.metric_smooth
  equation := fun _ ht x v w => R.metric_equation ht x v w

end Response

omit [MeasurableSpace M] [BorelSpace M] in

theorem exists_nativeDeTurckFamily (g0 : RiemannianMetric n M) :
    Nonempty (NativeDeTurckFamily g0) := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  obtain ⟨d⟩ := TensorHilbertNative.exists_data g0
  obtain ⟨L⟩ := exists_finiteChartLocalizationData d.charts
  have hp : (n : ℝ) < 2 * (2 * ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨R⟩ := exists_response d L (2 * (n + 1)) (n + 1) le_rfl hp
  exact ⟨R.nativeFamily⟩

omit [MeasurableSpace M] [BorelSpace M] in

theorem exists_metricFamily (g0 : RiemannianMetric n M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ (D : LeviCivitaData (g t))
        (x : M) (v w : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s => (g s).inner x v w)
          (-2 * D.ricci x v w) (Ico 0 T) t := by
  obtain ⟨R⟩ := exists_nativeDeTurckFamily g0
  exact DeTurckFamilyRecoveryNative.exists_metricFamily R.hT R.metric R.smooth R.initial R.equation

end PoincareConjecture.DeTurckResponseMetricNative

end

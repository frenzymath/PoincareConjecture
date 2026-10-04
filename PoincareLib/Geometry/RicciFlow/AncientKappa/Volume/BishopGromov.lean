import PoincareLib.Geometry.RicciFlow.AncientKappa.Volume.Theory
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareLib.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls

/-!
# Bishop--Gromov theory for ancient kappa-solution slices

The frozen calibrated positive-radius infimum agrees with the existing real
volume-ratio limit. Completeness and nonnegative Ricci curvature give radius
monotonicity and basepoint independence. The only supplied predecessor is
M04's static tensor calculus, applied to the actual slice connection.

Morgan--Tian, Theorem 1.34, pp. 19--20; Definition 9.1, pp. 180--181;
Chapter 9, Section 6, pp. 221--222.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

omit [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] in
/-- Finite calibrated ball ratios are the nonnegative real ball ratios. -/
theorem metricBallVolumeRatio_eq_ofReal (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (r : PositiveRadius) :
    metricBallVolumeRatio g p r =
      ENNReal.ofReal ((g.volumeMeasure (g.ball p r.1)).toReal / r.1 ^ n) := by
  rw [metricBallVolumeRatio, calibratedMetricVolume_eq_volumeMeasure,
    ENNReal.ofReal_div_of_pos (pow_pos r.2 n), ENNReal.ofReal_pow r.2.le,
    ENNReal.ofReal_toReal (g.ball_volume_ne_top_of_metricComplete hc p r.1)]

omit [T2Space M] [ConnectedSpace M] in
/-- Bishop--Gromov for the frozen calibrated positive-radius ratios. -/
theorem antitoneMetricBallVolumeRatio_of_nonneg_ricci
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) : AntitoneMetricBallVolumeRatio g p := by
  intro r s hrs
  rw [metricBallVolumeRatio_eq_ofReal g hc p s,
    metricBallVolumeRatio_eq_ofReal g hc p r]
  exact ENNReal.ofReal_le_ofReal
    (g.antitoneOn_ball_volume_div_pow D hn hc hRic p r.2 s.2 hrs)

omit [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] in
/-- An antitone calibrated ratio converges to its positive-radius infimum. -/
theorem hasAsymptoticVolumeRatio_of_antitone
    (g : RiemannianMetric n M) (p : M)
    (h : AntitoneMetricBallVolumeRatio g p) : HasAsymptoticVolumeRatio g p := by
  exact tendsto_atTop_iInf h

omit [T2Space M] [ConnectedSpace M] in
/-- The frozen infimum and the real asymptotic limit give the same volume. -/
theorem asymptoticVolumeRatio_eq_ofReal
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) :
    asymptoticVolumeRatio g p = ENNReal.ofReal (g.asymptoticVolumeRatio p) := by
  have hval : Tendsto (fun r : PositiveRadius => r.1) atTop atTop := by
    change map ((↑) : Ioi (0 : ℝ) → ℝ) atTop ≤ atTop
    rw [map_val_Ioi_atTop]
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((g.tendsto_asymptoticVolumeRatio D hn hc hRic p).comp hval)
  have hlim' : Tendsto (metricBallVolumeRatio g p) atTop
      (𝓝 (ENNReal.ofReal (g.asymptoticVolumeRatio p))) := by
    simpa only [Function.comp_def, ← metricBallVolumeRatio_eq_ofReal g hc p] using hlim
  exact tendsto_nhds_unique
    (hasAsymptoticVolumeRatio_of_antitone g p
      (antitoneMetricBallVolumeRatio_of_nonneg_ricci g D hn hc hRic p)) hlim'

omit [T2Space M] in
/-- Basepoint independence transported to the frozen positive-radius infimum. -/
theorem asymptoticVolumeRatioBasepointIndependent_of_nonneg_ricci
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    AsymptoticVolumeRatioBasepointIndependent g := by
  intro p q
  rw [asymptoticVolumeRatio_eq_ofReal g D hn hc hRic p,
    asymptoticVolumeRatio_eq_ofReal g D hn hc hRic q,
    g.asymptoticVolumeRatio_eq_of_preconnected D hn hc hRic p q]

/-- M21: each ancient slice has the frozen Bishop--Gromov and asymptotic-volume
properties, relative to its unchanged static tensor-calculus predecessor. -/
theorem asymptoticVolumeRatioBishopGromov (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n := by
  constructor
  intro M _ _ _ _ _ _ _ _ _ K t ht
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    obtain ⟨x, hx⟩ := K.nonflat t ht
    have : IsEmpty (Fin (Module.finrank ℝ (TangentSpace (𝓡 0) x))) := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 from
        finrank_euclideanSpace_fin]
      infer_instance
    exact hx (by simp [LeviCivitaData.curvatureTensorNorm])
  have hRic (x : M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ (K.flow.connection t).ricci x v v :=
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (P M (K.flow.metric t) (K.flow.connection t)) x
      (K.nonnegative_curvature_operator t ht x) v).1
  have hanti := antitoneMetricBallVolumeRatio_of_nonneg_ricci
    (K.flow.metric t) (K.flow.connection t) hn (K.complete t ht) hRic
  exact ⟨{
    time_mem := ht
    ratio_antitone := hanti
    ratio_limit := fun p => hasAsymptoticVolumeRatio_of_antitone _ p (hanti p)
    basepoint_independent := asymptoticVolumeRatioBasepointIndependent_of_nonneg_ricci
      (K.flow.metric t) (K.flow.connection t) hn (K.complete t ht) hRic
  }⟩

/-- Compatibility assembly for an explicitly supplied static service. -/
theorem asymptoticVolumeRatioTheory (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n P

end PoincareMT

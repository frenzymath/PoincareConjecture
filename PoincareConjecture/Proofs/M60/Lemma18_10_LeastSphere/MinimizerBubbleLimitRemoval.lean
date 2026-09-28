import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitCompactification
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityRemoval
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem suFiniteEnergyPlane_removed_weakCoordinate
    (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (hh : SUPlaneHarmonic g f)
    (hfinite : Integrable (m60EnergyDensity g f)) :
    ∃ (p : M) (R : ℝ), 0 < R ∧ R < 1 ∧
      let psi := Function.update (f ∘ suBubbleInversion) 0 p
      let u := extChartAt (𝓡 n) p ∘ psi
      ContinuousOn psi (Metric.ball (0 : LoopPlane) 1) ∧
      MapsTo psi (Metric.closedBall (0 : LoopPlane) R) (extChartAt (𝓡 n) p).source ∧
      SUWeakAlphaCoordinate g p 1 u (fun i z => fderiv ℝ u z (b i)) 0 R := by
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  have hi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (f ∘ suBubbleInversion)
      (Metric.ball (0 : LoopPlane) 1 \ {0}) := by
    intro z hz
    exact ((hf _).comp z
      (contMDiffAt_iff_contDiffAt.mpr (suBubbleInversion_geometry hz.2).1)).contMDiffWithinAt
  obtain ⟨p, R, q, hR, hR1, hq, hc, hm, huc, hum, hVm, hweak, hvar⟩ :=
    suHarmonicPuncture_removable_weak D hi
      (fun p z hz hp => suHarmonic_inversion g f hf hh p hz.2 hp)
      (suBubbleInversion_finite_energy g f (hf.of_le (by simp)) hfinite)
  let psi := Function.update (f ∘ suBubbleInversion) 0 p
  let u := extChartAt (𝓡 n) p ∘ psi
  let mu := volume.restrict (Metric.ball (0 : LoopPlane) R)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hq2 : ENNReal.ofReal (2 * (1 : ℝ)) ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨p, R, hR, hR1, hc, hm, ?_⟩
  exact ⟨hR, fun z hz => (extChartAt (𝓡 n) p).map_source (hm hz), huc,
    hum.mono_exponent hq2, fun i => (hVm i).mono_exponent hq2, hweak,
    fun eta he hc hs => (hvar eta he hc hs).1, fun eta he hc hs => (hvar eta he hc hs).2⟩

theorem suFiniteEnergyPlane_smooth_sphere
    (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hh : SUPlaneHarmonic g f) (hfinite : Integrable (m60EnergyDensity g f)) :
    ∃ sphere : UnitTwoSphere → M,
      ContMDiff (𝓡 2) (𝓡 n) ∞ sphere ∧ sphere ∘ m60SphereParameter = f ∧
      M60SphereChartHarmonic g sphere ∧
      m60SphereEnergy g sphere = ∫ z, m60EnergyDensity g f z := by
  obtain ⟨p, R, _, _, hc, hm, S⟩ := suFiniteEnergyPlane_removed_weakCoordinate g f hf hh hfinite
  let psi := Function.update (f ∘ suBubbleInversion) 0 p
  let u := extChartAt (𝓡 n) p ∘ psi
  have huc : ContDiffAt ℝ ∞ u 0 := regular p u _ 0 R S
  have hps : psi 0 ∈ (extChartAt (𝓡 n) p).source :=
    hm (Metric.mem_closedBall_self S.radius_pos.le)
  have hpc : ContinuousAt psi 0 := hc.continuousAt
    (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  have hzero : ContMDiffAt (𝓡 2) (𝓡 n) ∞ psi 0 := by
    have hi := (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ((extChartAt (𝓡 n) p).map_source hps))
    apply (hi.comp 0 (contMDiffAt_iff_contDiffAt.mpr huc)).congr_of_eventuallyEq
    filter_upwards [hpc ((isOpen_extChartAt_source p).mem_nhds hps)] with z hz
    exact ((extChartAt (𝓡 n) p).left_inv hz).symm
  exact ⟨suSphereFromPlane f p, suSphereFromPlane_smooth f p hf hzero,
    suSphereFromPlane_parameter f p, suSphereFromPlane_harmonic g f p hh,
    suSphereFromPlane_energy g f p⟩

theorem suFiniteEnergyPlane_smooth_sphere_of_finite_energy
    (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hh : SUPlaneHarmonic g f) (hfinite : Integrable (m60EnergyDensity g f)) :
    ∃ sphere : UnitTwoSphere → M,
      ContMDiff (𝓡 2) (𝓡 n) ∞ sphere ∧ sphere ∘ m60SphereParameter = f ∧
      M60SphereChartHarmonic g sphere ∧
      m60SphereEnergy g sphere = ∫ z, m60EnergyDensity g f z :=
  suFiniteEnergyPlane_smooth_sphere g (suWeakAlphaCoordinate_smooth_alpha_one g)
    f hf hh hfinite

end PoincareConjecture.M60

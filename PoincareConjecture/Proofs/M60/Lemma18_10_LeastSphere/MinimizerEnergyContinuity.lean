import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem suC1_intrinsicEnergy_continuous (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    Continuous (m60SphereIntrinsicEnergy g f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := chartAt LoopPlane p
  have hplane : Continuous (m60EnergyDensity g (f ∘ e.symm)) :=
    m60EnergyDensity_continuous g (hf.comp ((suSphereChart_smooth p).of_le (by simp)))
  have hfactor : Continuous (fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2) :=
    continuous_const.div₀ (((continuous_norm.pow 2).add continuous_const).pow 2)
      (fun _ => by positivity)
  have hlocal : ContinuousAt (fun x =>
      m60EnergyDensity g (f ∘ e.symm) (e x) / (16 / (‖e x‖ ^ 2 + 4) ^ 2)) p :=
    ((hplane.div₀ hfactor (fun _ => by positivity)).continuousAt).comp
      (e.continuousAt (mem_chart_source LoopPlane p))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds (mem_chart_source LoopPlane p)] with x hx
  rw [suSphereChart_energy g f hf p, e.left_inv hx]
  exact (mul_div_cancel_right₀ _
    (show (16 : ℝ) / (‖e x‖ ^ 2 + 4) ^ 2 ≠ 0 by positivity)).symm



theorem suC1_energy_eq_intrinsic_integral (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    m60SphereEnergy g f =
      ∫ p, m60SphereIntrinsicEnergy g f p ∂m60RoundSphereMetric.volumeMeasure := by
  rw [m60RoundSphereMetric_integral _ (suC1_intrinsicEnergy_continuous g hf)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => m60SphereEnergyDensity_eq_intrinsic_mul g f hf z




theorem suC1_energy_le_of_density_le (g : RiemannianMetric n M)
    {f h : UnitTwoSphere → M}
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (hh : ContMDiff (𝓡 2) (𝓡 n) 1 h)
    (eta : ℝ)
    (hle : ∀ p, m60SphereIntrinsicEnergy g h p ≤ m60SphereIntrinsicEnergy g f p + eta) :
    m60SphereEnergy g h ≤ m60SphereEnergy g f + eta * (4 * Real.pi) := by
  have hfint := (suC1_intrinsicEnergy_continuous g hf).integrable_of_hasCompactSupport
    (μ := m60RoundSphereMetric.volumeMeasure)
    (HasCompactSupport.of_compactSpace _)
  have hhint := (suC1_intrinsicEnergy_continuous g hh).integrable_of_hasCompactSupport
    (μ := m60RoundSphereMetric.volumeMeasure)
    (HasCompactSupport.of_compactSpace _)
  rw [suC1_energy_eq_intrinsic_integral g hf, suC1_energy_eq_intrinsic_integral g hh]
  calc
    _ ≤ ∫ p, m60SphereIntrinsicEnergy g f p + eta ∂m60RoundSphereMetric.volumeMeasure :=
      integral_mono hhint (hfint.add (integrable_const eta)) hle
    _ = _ := by
      rw [integral_add hfint (integrable_const eta), integral_const,
        smul_eq_mul, m60RoundSphereMetric_volume_univ]
      ring

end PoincareConjecture.M60

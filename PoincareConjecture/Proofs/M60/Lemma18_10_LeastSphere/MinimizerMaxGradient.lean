import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRoundFactor
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerEnergyContinuity
import PoincareConjecture.Proofs.M36.CylinderGram
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suSphereGradient_exists_max (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    ∃ p : UnitTwoSphere, ∀ x : UnitTwoSphere,
      2 * m60SphereIntrinsicEnergy g f x ≤ 2 * m60SphereIntrinsicEnergy g f p := by
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set UnitTwoSphere).Nonempty from ⟨m60SpherePole, Set.mem_univ _⟩)
    (continuous_const.mul (suC1_intrinsicEnergy_continuous g hf)).continuousOn
  exact ⟨p, fun x => hp (Set.mem_univ x)⟩

theorem suSphereChart_symm_zero (p : UnitTwoSphere) :
    (chartAt LoopPlane p).symm 0 = p := by
  rw [← M36.sphere_chart_center_zero p]
  exact (chartAt LoopPlane p).left_inv (mem_chart_source LoopPlane p)

theorem suSphere_rescaled_density (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (p : UnitTwoSphere) (s : ℝ) (z : LoopPlane) :
    m60EnergyDensity g (fun y => f ((chartAt LoopPlane p).symm (s • y))) z =
      s ^ 2 * m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm (s • z)) *
        suAlphaRoundFactor (s • z) := by
  have h := suRescale_energyDensity g (f ∘ (chartAt LoopPlane p).symm)
    ((hf.comp ((suSphereChart_smooth p).of_le (by simp))).mdifferentiable (by simp)) 0 s z
  simp only [zero_add, Function.comp_apply] at h
  rw [h, suSphereChart_energy g f hf p]
  exact (mul_assoc _ _ _).symm

theorem suSphere_rescaled_energy (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (p : UnitTwoSphere) {s : ℝ} (hs : 0 < s) :
    let v := fun z : LoopPlane => f ((chartAt LoopPlane p).symm (s • z))
    Integrable (m60EnergyDensity g v) ∧
      (∫ z, m60EnergyDensity g v z) = m60SphereEnergy g f := by
  intro v
  have hc := suC1_intrinsicEnergy_continuous g hf
  have hi := suSphereChart_integrable p _ hc
  have hiden : Integrable (m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm)) := by
    have heq : m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm) =
        fun z => m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm z) *
          (16 / (‖z‖ ^ 2 + 4) ^ 2) := funext (suSphereChart_energy g f hf p)
    rw [heq]
    exact hi
  have hscale : m60EnergyDensity g v = fun z =>
      s ^ 2 * m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm) (s • z) := by
    funext z
    simpa only [zero_add, Function.comp_apply, v] using
      suRescale_energyDensity g (f ∘ (chartAt LoopPlane p).symm)
        ((hf.comp ((suSphereChart_smooth p).of_le (by simp))).mdifferentiable
          (by simp)) 0 s z
  constructor
  · rw [hscale]
    exact (hiden.comp_smul hs.ne').const_mul _
  · rw [hscale]
    have ht := suRescale_integral
      (m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm)) 0 hs Set.univ
    have hsurj : Function.Surjective (fun z : LoopPlane => (0 : LoopPlane) + s • z) := by
      intro z
      refine ⟨s⁻¹ • z, ?_⟩
      simp only [zero_add, smul_inv_smul₀ hs.ne']
    rw [Set.image_univ_of_surjective hsurj, setIntegral_univ, setIntegral_univ] at ht
    simp only [zero_add] at ht
    rw [ht, suC1_energy_eq_intrinsic_integral g hf, suSphereChart_integral p _ hc]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => suSphereChart_energy g f hf p z

theorem suSphere_maximum_normalization (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (p : UnitTwoSphere)
    (hmax : ∀ x, 2 * m60SphereIntrinsicEnergy g f x ≤
      2 * m60SphereIntrinsicEnergy g f p)
    (hpos : 0 < 2 * m60SphereIntrinsicEnergy g f p) :
    let s := (Real.sqrt (2 * m60SphereIntrinsicEnergy g f p))⁻¹
    let v := fun z : LoopPlane => f ((chartAt LoopPlane p).symm (s • z))
    0 < s ∧
      (∀ z, 0 ≤ 2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) ∧
        2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) ≤ 1) ∧
      m60EnergyDensity g v 0 = 1 / 2 ∧
      (∀ z, m60EnergyDensity g v z ≤ 1 / 2) := by
  intro s v
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hpos)
  have hnorm : s ^ 2 * (2 * m60SphereIntrinsicEnergy g f p) = 1 := by
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hq (z : LoopPlane) :
      2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) =
        s ^ 2 * (2 * m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm (s • z))) := by
    rw [suSphere_rescaled_density g hf p s z]
    field_simp [(suRoundFactor_smooth_pos.2 (s • z)).ne']
  have hbound (z : LoopPlane) :
      2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) ≤ 1 := by
    rw [hq]
    exact (mul_le_mul_of_nonneg_left (hmax _) (sq_nonneg s)).trans_eq hnorm
  refine ⟨hs, fun z => ⟨?_, hbound z⟩, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (m60EnergyDensity_nonneg g v z))
      (suRoundFactor_smooth_pos.2 _).le
  · have h := hq 0
    simp only [smul_zero, suSphereChart_symm_zero, suAlphaRoundFactor, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add] at h
    norm_num at h
    nlinarith [hnorm]
  · intro z
    have hfactor : suAlphaRoundFactor (s • z) ≤ 1 := by
      unfold suAlphaRoundFactor
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg ‖s • z‖]
    have h := (div_le_iff₀ (suRoundFactor_smooth_pos.2 (s • z))).mp (hbound z)
    nlinarith

theorem suNormalized_disk_energy_le (g : RiemannianMetric n M)
    {v : LoopPlane → M} (hv : ContMDiff (𝓡 2) (𝓡 n) 1 v)
    (hbound : ∀ z, m60EnergyDensity g v z ≤ 1 / 2)
    (a : LoopPlane) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (m60EnergyDensity g v) (Metric.closedBall a R) ∧
      (∫ z in Metric.closedBall a R, m60EnergyDensity g v z) ≤ Real.pi * R ^ 2 / 2 := by
  have hi : IntegrableOn (m60EnergyDensity g v) (Metric.closedBall a R) :=
    (m60EnergyDensity_continuous g hv).continuousOn.integrableOn_compact
    (isCompact_closedBall a R)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _ in Metric.closedBall a R, (1 / 2 : ℝ) :=
      setIntegral_mono_on hi
        (integrableOn_const (isCompact_closedBall a R).measure_lt_top.ne)
        measurableSet_closedBall
        (fun z _ => hbound z)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, EuclideanSpace.volume_closedBall_fin_two,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
        ENNReal.toReal_ofReal Real.pi_pos.le]
      ring

end PoincareConjecture.M60

end

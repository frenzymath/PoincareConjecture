import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.ModelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Data

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace DeepHorn

def neckVolumeRadius : ℝ := 2 * Real.pi + 3

def neckVolumeConstant : ℝ := roundCylinderCrossSectionArea.toReal / 4

theorem neckVolumeRadius_pos : 0 < neckVolumeRadius := by
  unfold neckVolumeRadius
  positivity

theorem neckVolumeConstant_pos : 0 < neckVolumeConstant :=
  div_pos roundCylinderCrossSectionArea_toReal_pos (by norm_num)

end DeepHorn

namespace EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem central_unit_slab_subset_ball :
    N.coordinate_map '' ((univ : Set UnitTwoSphere) ×ˢ Ioo (-1 : ℝ) 1) ⊆
      g.ball N.center (DeepHorn.neckVolumeRadius * N.scale) := by
  rintro x ⟨z, hz, rfl⟩
  have hinv : (1 : ℝ) < N.epsilon⁻¹ := by
    exact (one_lt_inv₀ N.epsilon_pos).mpr (by linarith [N.epsilon_lt_half])
  have hdomain : z ∈ N.cylinderDomain :=
    ⟨hz.1, by linarith [hz.2.1], hz.2.2.trans hinv⟩
  have hx := N.coordinate_map_mem hdomain
  have hdist := N.edist_central_sphere_le_of_mem_carrier hx N.center_on_central_sphere
  rw [N.coordinate_inverse_coordinate_map hdomain] at hdist
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change g.edist N.center (N.coordinate_map z) < _
  have hcomm : g.edist N.center (N.coordinate_map z) =
      g.edist (N.coordinate_map z) N.center := Manifold.riemannianEDist_comm
  rw [hcomm]
  apply hdist.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos DeepHorn.neckVolumeRadius_pos N.scale_pos)).mpr
  apply mul_lt_mul_of_pos_right _ N.scale_pos
  have haxis : |z.2| < 1 := abs_lt.mpr hz.2
  unfold DeepHorn.neckVolumeRadius
  linarith

theorem volume_center_ball_lower :
    ENNReal.ofReal (DeepHorn.neckVolumeConstant * N.scale ^ 3) ≤
      g.volumeMeasure (g.ball N.center (DeepHorn.neckVolumeRadius * N.scale)) := by
  have hinv : (1 : ℝ) < N.epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (by linarith [N.epsilon_lt_half])
  have hdomain : (univ : Set UnitTwoSphere) ×ˢ Ioo (-1 : ℝ) 1 ⊆ N.cylinderDomain := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hq, by linarith [ht.1], ht.2.trans hinv⟩
  have hmodel : roundCylinderVolumeMeasure
      ((univ : Set UnitTwoSphere) ×ˢ Ioo (-1 : ℝ) 1) =
        roundCylinderCrossSectionArea * 2 := by
    rw [roundCylinderVolumeMeasure_eq_prod, Measure.prod_prod]
    norm_num [roundCylinderCrossSectionArea]
  have hcompare := (N.volumeMeasure_image_bounds
    (MeasurableSet.univ.prod measurableSet_Ioo) hdomain).1
  rw [hmodel] at hcompare
  apply le_trans _ (hcompare.trans (measure_mono N.central_unit_slab_subset_ball))
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [N.epsilon_lt_half, Real.sqrt_nonneg (1 - N.epsilon)]
  have hfactor : N.scale / 2 ≤ N.scale * Real.sqrt (1 - N.epsilon) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hroot N.scale_pos.le
  have hreal : DeepHorn.neckVolumeConstant * N.scale ^ 3 =
      (N.scale / 2) ^ 3 * (roundCylinderCrossSectionArea.toReal * 2) := by
    unfold DeepHorn.neckVolumeConstant
    ring
  have hscale : 0 ≤ N.scale / 2 := div_nonneg N.scale_pos.le (by norm_num)
  rw [hreal, ENNReal.ofReal_mul (pow_nonneg hscale 3), ENNReal.ofReal_pow hscale,
    ENNReal.ofReal_mul roundCylinderCrossSectionArea_toReal_pos.le,
    ENNReal.ofReal_toReal roundCylinderCrossSectionArea_lt_top.ne]
  norm_num only [ENNReal.ofReal_ofNat]
  gcongr

end EpsilonNeck

namespace GeneralizedStrongNeck

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

theorem scale_eq_inv_sqrt_scalar (N : GeneralizedStrongNeck F t epsilon) :
    N.scale = (Real.sqrt (F.scalar ⟨t, N.center⟩))⁻¹ := by
  rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  rfl

theorem calibratedVolume_center_ball_lower (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) :
    ENNReal.ofReal (DeepHorn.neckVolumeConstant /
        (Real.sqrt (F.scalar ⟨t, N.center⟩)) ^ 3) ≤
      calibratedMetricVolume (F.metric t)
        ((F.metric t).ball N.center
          (DeepHorn.neckVolumeRadius / Real.sqrt (F.scalar ⟨t, N.center⟩))) := by
  have h := (N.spatialNeck hepsilon).volume_center_ball_lower
  change ENNReal.ofReal (DeepHorn.neckVolumeConstant * N.scale ^ 3) ≤
    (F.metric t).volumeMeasure
      ((F.metric t).ball N.center (DeepHorn.neckVolumeRadius * N.scale)) at h
  rw [N.scale_eq_inv_sqrt_scalar, ← div_eq_mul_inv,
    inv_pow, ← div_eq_mul_inv] at h
  rw [Generalized.Noncollapse.calibratedMetricVolume_eq_euclideanHausdorff]
  exact h

end GeneralizedStrongNeck

namespace GeneralizedBlowupSequence

theorem terminal_volume_of_strongNecks (S : GeneralizedBlowupSequence.{u})
    (hneck : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ epsilon : ℝ, epsilon < 1 / 2 ∧
        ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 epsilon,
          N.center = (S.base k).2) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho) := by
  refine ⟨DeepHorn.neckVolumeRadius, DeepHorn.neckVolumeConstant,
    DeepHorn.neckVolumeRadius_pos, DeepHorn.neckVolumeConstant_pos, ?_⟩
  filter_upwards [hneck] with k hk
  obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hk
  simpa only [GeneralizedBlowupSequence.baseBall, GeneralizedBlowupSequence.scale,
    hcenter, Sigma.eta] using N.calibratedVolume_center_ball_lower hepsilon

end GeneralizedBlowupSequence

end PoincareConjecture

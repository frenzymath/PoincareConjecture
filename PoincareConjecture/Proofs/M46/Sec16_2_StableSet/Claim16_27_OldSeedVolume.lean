import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedImage
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedScales
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M04.LocalMetricComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



theorem old_seed_image_volume
    (P : M44CapPersistencePredecessors.{u}) {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hpinch : SurgeryFlowPinched F)
    {t B : ℝ} (ht : t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (x : (F.slice t).carrier) (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hB : 1 ≤ B)
    (e : SurgeryFlowCylinder F (F.slice t) t 1
      (Icc (-seedCylinderDuration B (p.r (Fin.last p.i))) 0)
      ((F.metric t).ball x (p.r (Fin.last p.i) / (8 * B))))
    (hbase : ∀ h y, y ∈ (F.metric t).ball x (p.r (Fin.last p.i) / (8 * B)) →
      HEq (e.forward 0 h y) y)
    (hRm : ∀ s hs y, y ∈ (F.metric t).ball x (p.r (Fin.last p.i) / (8 * B)) →
      (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤
        52 * (p.r (Fin.last p.i))⁻¹ ^ 2) :
    ∃ hs : -seedImageDelay B (p.r (Fin.last p.i)) ∈
        Icc (-seedCylinderDuration B (p.r (Fin.last p.i))) 0,
      let A := e.forward (-seedImageDelay B (p.r (Fin.last p.i))) hs ''
        (F.metric t).ball x (seedImageRadius B (p.r (Fin.last p.i)))
      IsOpen A ∧ IsCompact (closure A) ∧
        closure A ⊆ m33RegularRegion F (t + -seedImageDelay B (p.r (Fin.last p.i)) / 1) ∧
        ENNReal.ofReal (p.kappa (Fin.last p.i) *
          seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8) ≤
          calibratedMetricVolume
            (F.metric (t + -seedImageDelay B (p.r (Fin.last p.i)) / 1)) A := by
  let r := p.r (Fin.last p.i)
  let rho := seedImageRadius B r
  have hr : 0 < r := p.r_pos _
  have hrho : 0 < rho := seedImageRadius_pos hB hr
  have hrhole : rho ≤ F.parameters.epsilon := by
    rw [old.epsilon_eq]
    exact (seedImageRadius_le hB hr).trans (p.r_le_epsilon _)
  have hbuffer : closure ((F.metric t).ball x rho) ⊆ (F.metric t).ball x (r / (8 * B)) := by
    have hhalf := M04.initial_half_ball_closure_subset_initial_ball (F.metric t) x
      (by positivity : 0 < 2 * rho)
    rw [show 2 * rho / 2 = rho by ring] at hhalf
    intro y hy
    exact (hhalf hy).trans_le
      (ENNReal.ofReal_le_ofReal (twice_seedImageRadius_lt_ball_radius hB hr).le)
  have hsource := subset_closure.trans hbuffer
  have hJ : Icc (-rho ^ 2) 0 ⊆ Icc (-seedCylinderDuration B r) 0 :=
    Icc_subset_Icc_left (neg_le_neg (seedImageRadius_sq_le_duration hB hr))
  let test := e.restrict hJ ordConnected_Icc hsource
  have hvolume : ENNReal.ofReal (p.kappa (Fin.last p.i) * rho ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball x rho) := by
    apply old.noncollapsed (Fin.last p.i) (by simp) t ht (O.interval_subset ht.1)
      x hpositive rho hrho hrhole test
    · intro h y hy
      exact hbase _ y (hsource hy)
    · intro s hs y hy
      exact (hRm s (hJ hs) y (hsource hy)).trans (seedImageRadius_curvature_bound hB hr)
  have hseed : -seedImageDelay B r ∈ Ioc (-seedCylinderDuration B r) 0 :=
    ⟨neg_lt_neg (seedImageDelay_lt_duration hB hr),
      neg_nonpos.mpr (seedImageDelay_pos hB hr).le⟩
  refine ⟨Ioc_subset_Icc_self hseed, ?_⟩
  apply controlled_cylinder_seed_image P hpinch e (M04.initial_ball_isOpen _ _ _) hbase
    hseed _ hRm (M04.initial_ball_isOpen _ _ _)
    ((F.slices_compact t (O.interval_subset ht.1)).of_isClosed_subset isClosed_closure
      (subset_univ _)) hbuffer hvolume
  simpa only [neg_neg] using seedImageDelay_metric_short hB hr

end PoincareConjecture.Proofs.M46

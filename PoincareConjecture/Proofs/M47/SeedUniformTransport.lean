import PoincareConjecture.Proofs.M47.SeedTube
import PoincareConjecture.Proofs.M47.SeedPathChain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_old_prefix_uniform_seed_transport (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    (H L k0 : ℝ) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) (hk0 : 0 < k0) :
    ∃ d k : ℝ, 0 < d ∧ 0 < k ∧ d ≤ (Real.sqrt H)⁻¹ ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ t ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
          ∀ gamma : ℝ → (F.slice t).carrier,
            ContinuousOn gamma (Icc 0 1) →
            ¬ SurgeryPositiveComponentAt F t (gamma 0) →
            (∀ v ∈ Icc (0 : ℝ) 1,
              (F.connection t).scalarCurvature (gamma v) ≤ H) →
            (∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
              (F.metric t).edist (gamma v) (gamma w) ≤
                ENNReal.ofReal (L * |v - w|)) →
            ENNReal.ofReal (k0 * d ^ 3) ≤ calibratedMetricVolume (F.metric t)
              ((F.metric t).ball (gamma 0) d) →
            ENNReal.ofReal (k * d ^ 3) ≤ calibratedMetricVolume (F.metric t)
              ((F.metric t).ball (gamma 1) d) := by
  have hH : 0 < H :=
    (pow_pos (inv_pos.mpr (p.r_pos (Fin.last p.i))) 2).trans_le hlevel
  let B := max 1 (M46.seedAnalyticConstant S)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hB : M46.seedAnalyticConstant S ≤ B := le_max_right _ _
  let s := (Real.sqrt H)⁻¹
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  let tube := s / (8 * B)
  have htube : 0 < tube := seed_tube_radius_pos S hH hB
  have htubes : tube ≤ s := div_le_self hs.le (by linarith)
  let d := tube / 4
  have hd : 0 < d := div_pos htube (by norm_num)
  have hdTube : 2 * d ≤ tube := by dsimp only [d]; linarith
  have hds : d ≤ s := (by dsimp only [d]; linarith : d ≤ tube).trans htubes
  let K := 13 * max (2 * H) (Real.exp 4)
  have hK : 0 < K := mul_pos (by norm_num)
    ((Real.exp_pos 4).trans_le (le_max_right _ _))
  let A := 2 * d * Real.sqrt K
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) hd) (Real.sqrt_pos.mpr hK)
  have hAnorm : (A / (2 * d)) ^ 2 = K := by
    dsimp only [A]
    rw [mul_div_cancel_left₀ _ (show 2 * d ≠ 0 by positivity), Real.sq_sqrt hK.le]
  let k := seedBallStepLoss A ^ seedChainSteps L d * k0
  have hk : 0 < k := mul_pos (pow_pos (seedBallStepLoss_bounds A).1 _) hk0
  refine ⟨d, k, hd, hk, hds, ?_⟩
  intro F O old t ht gamma hgamma hpositive hscalar hspeed hvolume
  let : CompactSpace (F.slice t).carrier :=
    isCompact_univ_iff.mp (F.slices_compact t (O.interval_subset ht.1))
  have htubesBound := seed_path_tube_bounds P S F t hH hlevel hB
    (old_prefix_seed_canonical S p compatible old ht)
    (old.pinched t ht.1 (O.interval_subset ht.1)) gamma hgamma hpositive hscalar
  have hcurv : ∀ v ∈ Icc (0 : ℝ) 1, ∀ z ∈ (F.metric t).ball (gamma v) (2 * d),
      (F.connection t).curvatureTensorNorm z ≤ (A / (2 * d)) ^ 2 := by
    intro v hv z hz
    rw [hAnorm]
    exact (htubesBound v hv z (hz.trans_le (ENNReal.ofReal_le_ofReal hdTube))).2
  exact seed_path_volume_transport (F.metric t) (F.connection t) gamma hA hd hk0
    hspeed (fun _ _ => isClosed_closure.isCompact) hcurv hvolume

end PoincareConjecture.Proofs.M47

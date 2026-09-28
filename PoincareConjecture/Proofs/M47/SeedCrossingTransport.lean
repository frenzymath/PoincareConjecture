import PoincareConjecture.Proofs.M47.SeedTube
import PoincareConjecture.Proofs.M47.SeedPathChain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_old_prefix_crossing_transport (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    (H L : ℝ) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) :
    ∃ d k : ℝ, 0 < d ∧ 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ t ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
          ∀ gamma : ℝ → (F.slice t).carrier,
            ContinuousOn gamma (Icc 0 1) →
            ¬ SurgeryPositiveComponentAt F t (gamma 0) →
            (F.connection t).scalarCurvature (gamma 0) = H →
            (∀ s ∈ Icc (0 : ℝ) 1,
              (F.connection t).scalarCurvature (gamma s) ≤ H) →
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
              (F.metric t).edist (gamma s) (gamma v) ≤
                ENNReal.ofReal (L * |s - v|)) →
            ENNReal.ofReal (k * d ^ 3) ≤ calibratedMetricVolume (F.metric t)
              ((F.metric t).ball (gamma 1) d) := by
  have hrho := p.r_pos (Fin.last p.i)
  have hH : 0 < H := (pow_pos (inv_pos.mpr hrho) 2).trans_le hlevel
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
  let k := seedBallStepLoss A ^ seedChainSteps L d * canonicalSeedDensity S.setup.C
  have hk : 0 < k := mul_pos (pow_pos (seedBallStepLoss_bounds A).1 _)
    (canonicalSeedDensity_pos _)
  refine ⟨d, k, hd, hk, ?_⟩
  intro F O old t ht gamma hgamma hpositive hcross hscalar hspeed
  have htF := O.interval_subset ht.1
  let : CompactSpace (F.slice t).carrier := isCompact_univ_iff.mp (F.slices_compact t htF)
  have hC : F.parameters.C = S.setup.C := by rw [old.C_eq, compatible.setup_eq]
  have hcanonical := old_prefix_seed_canonical S p compatible old ht
  have hpinch := old.pinched t ht.1 htF
  have hhigh : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤
      (F.connection t).scalarCurvature (gamma 0) := by rwa [hcross]
  have hcanon : SurgeryCanonicalControl F t (gamma 0)
      F.parameters.epsilon F.parameters.C := by
    rw [hC]
    exact hcanonical (gamma 0) hhigh
  have hrhoSmall : p.r (Fin.last p.i) ≤ 1 / 200 :=
    (p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))
  have hsq : s⁻¹ ^ 2 = H := by dsimp only [s]; rw [inv_inv, Real.sq_sqrt hH.le]
  have hinverse : s⁻¹ ≤ d⁻¹ := (inv_le_inv₀ hs hd).mpr hds
  have htest : (F.connection t).scalarCurvature (gamma 0) ≤ 9 * d⁻¹ ^ 2 := by
    have hpower := pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hinverse 2
    rw [hsq] at hpower
    rw [hcross]
    nlinarith [sq_nonneg d⁻¹]
  have hvolume := canonical_seed_volume P hcanon hpositive hrho hrhoSmall hhigh
    hpinch hd htest
  rw [hC] at hvolume
  have htubesBound := seed_path_tube_bounds P S F t hH hlevel hB hcanonical
    hpinch gamma hgamma hpositive hscalar
  have hcurv : ∀ v ∈ Icc (0 : ℝ) 1, ∀ z ∈ (F.metric t).ball (gamma v) (2 * d),
      (F.connection t).curvatureTensorNorm z ≤ (A / (2 * d)) ^ 2 := by
    intro v hv z hz
    rw [hAnorm]
    exact (htubesBound v hv z (hz.trans_le (ENNReal.ofReal_le_ofReal hdTube))).2
  exact seed_path_volume_transport (F.metric t) (F.connection t) gamma hA hd
    (canonicalSeedDensity_pos _) hspeed (fun _ _ => isClosed_closure.isCompact)
    hcurv hvolume

end PoincareConjecture.Proofs.M47

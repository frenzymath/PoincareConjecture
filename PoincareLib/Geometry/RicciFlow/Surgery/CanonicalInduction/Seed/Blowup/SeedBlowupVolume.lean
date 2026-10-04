import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Blowup.SeedBlowupVolumeCylinder
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.Transport.HistoryMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseGeometry

/-!
# Actual generalized terminal volume in blowup units

The physical tested volume and the retained whole-ball identity use the
same selected M33 history. Source: MT Claim 17.9, pp. 406-407;
seed-blowup-terminal-volume.md.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M47

/-- The normalized test gives the literal generalized ball volume,
without replacing it by only the forward image of an intrinsic ball. -/
theorem seed_blowup_terminal_volume {F : SurgeryFlowData.{u}}
    {W : M33RegularHistoryWindow F} (H : M33RegularHistoryData W)
    {J : Set ℝ} {k t Q tau rho B : ℝ}
    (volume : SurgeryVolumeControlOn F J k (fun _ _ => True))
    (htJ : t ∈ J) (ht : t ∈ H.generalized.interval)
    (hQ : 0 < Q) (hrho : 0 < rho) (htime : rho ^ 2 ≤ tau)
    (hbound : B ≤ rho⁻¹ ^ 2) (hsmall : rho / Real.sqrt Q ≤ F.parameters.epsilon)
    (x : (H.generalized.slice t).carrier)
    (e : SurgeryFlowCylinder F (F.slice t) t Q (Icc (-tau) 0)
      ((F.metric t).ball (H.history.forward t ht x) (rho / Real.sqrt Q)))
    (hbase : ∀ h y, y ∈ (F.metric t).ball (H.history.forward t ht x)
        (rho / Real.sqrt Q) → HEq (e.forward 0 h y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric t).ball (H.history.forward t ht x)
        (rho / Real.sqrt Q) →
      (F.connection (t + s / Q)).curvatureTensorNorm (e.forward s hs y) ≤ B * Q) :
    ENNReal.ofReal ((k * rho ^ 3) / (Real.sqrt Q) ^ 3) ≤
      calibratedMetricVolume (H.generalized.metric t)
        ((H.generalized.metric t).ball x (rho / Real.sqrt Q)) := by
  obtain ⟨test, based, curvature, regular⟩ :=
    exists_seed_blowup_volume_test hQ hrho htime hbound (H.history.forward t ht x)
      e hbase hcurv
  have hr : 0 < rho / Real.sqrt Q := div_pos hrho (Real.sqrt_pos.mpr hQ)
  have hzero : (0 : ℝ) ∈ Icc (-(rho / Real.sqrt Q) ^ 2) 0 :=
    ⟨neg_nonpos.mpr (sq_nonneg _), le_rfl⟩
  have htF : t ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using test.time_subset (mem_image_of_mem _ hzero)
  rw [H.ball_volume_of_subset t ht x _ regular]
  simpa only [div_pow, mul_div_assoc] using
    volume t htJ htF (H.history.forward t ht x) trivial _ hr hsmall test based curvature

/-- The radius and positive M30 volume constant are selected before the
physical flow, its chosen history, its base time and its scalar scale. -/
theorem exists_seed_blowup_terminal_volume_constants {k tau B : ℝ}
    (hk : 0 < k) (htau : 0 < tau) (hB : 0 ≤ B) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧
      ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F)
        (H : M33RegularHistoryData W) (J : Set ℝ),
        SurgeryVolumeControlOn F J k (fun _ _ => True) →
      ∀ (t Q : ℝ), t ∈ J → ∀ ht : t ∈ H.generalized.interval,
        0 < Q → rho / Real.sqrt Q ≤ F.parameters.epsilon →
      ∀ (x : (H.generalized.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t Q (Icc (-tau) 0)
          ((F.metric t).ball (H.history.forward t ht x) (rho / Real.sqrt Q))),
        (∀ h y, y ∈ (F.metric t).ball (H.history.forward t ht x)
          (rho / Real.sqrt Q) → HEq (e.forward 0 h y) y) →
        (∀ s hs y, y ∈ (F.metric t).ball (H.history.forward t ht x)
            (rho / Real.sqrt Q) →
          (F.connection (t + s / Q)).curvatureTensorNorm (e.forward s hs y) ≤ B * Q) →
        ENNReal.ofReal (v / (Real.sqrt Q) ^ 3) ≤
          calibratedMetricVolume (H.generalized.metric t)
            ((H.generalized.metric t).ball x (rho / Real.sqrt Q)) := by
  obtain ⟨rho, hrho, htime, hbound⟩ := exists_seed_blowup_test_radius htau hB
  refine ⟨rho, k * rho ^ 3, hrho, mul_pos hk (pow_pos hrho _), ?_⟩
  intro F W H J volume t Q htJ ht hQ hsmall x e hbase hcurv
  exact seed_blowup_terminal_volume H volume htJ ht hQ hrho htime hbound hsmall
    x e hbase hcurv

end PoincareMT.Proofs.M47

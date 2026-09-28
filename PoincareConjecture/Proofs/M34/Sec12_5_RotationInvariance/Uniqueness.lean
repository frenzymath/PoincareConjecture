import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.IndexedEnergyBounds
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.IndexedEnergyZero
import PoincareConjecture.Proofs.M34.Mathlib.FiniteNeighborEnergyZero












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem partialStandardCapFlow_metric_unique (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F F' : PartialStandardCapFlow g0) (e : StandardCylindricalEnd g0.metric)
    {t : ℝ} (ht : t ∈ Ico 0 F.lifetime ∩ Ico 0 F'.lifetime) :
    F.flow.metric t = F'.flow.metric t := by
  classical
  obtain ⟨S, htS, hSmin⟩ := exists_between (lt_min ht.1.2 ht.2.2)
  have hS : 0 < S := ht.1.1.trans_lt htS
  have hSF : S < F.lifetime := hSmin.trans_le (min_le_left _ _)
  have hSF' : S < F'.lifetime := hSmin.trans_le (min_le_right _ _)
  obtain ⟨B0, _hB0, hb0⟩ := F.curvature_locally_bounded S hS.le hSF
  obtain ⟨B1, _hB1, hb1⟩ := F'.curvature_locally_bounded S hS.le hSF'
  let B := max 1 (max B0 B1)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hf (s) (hs : s ∈ Ico 0 S) (x) : (F.flow.connection s).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans ((hb0 s ⟨hs.1, hs.2.le⟩ x).trans
      ((le_max_left _ _).trans (le_max_right _ _)))
  have hf' (s) (hs : s ∈ Ico 0 S) (x) : (F'.flow.connection s).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans ((hb1 s ⟨hs.1, hs.2.le⟩ x).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  let qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FH 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FA 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FS 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let p : endReferenceRegion e := Classical.choice inferInstance
  let E := capDifferenceEnergy e qH qA qS F.flow F'.flow p
  let D := capDifferenceSupportIntegral e qH qA qS F.flow F'.flow p
  obtain ⟨M, L, _hM, hL, hvalue, hrate⟩ := partialFlows_capDifferenceEnergy_bounds
    P E0 F F' e qH qA qS hS hSF.le hSF'.le hB hf hf' p
  obtain ⟨C, hC, hsupport⟩ := exists_capDifferenceSupportIntegral_bound e qH qA qS
  have hclosed (s) (hs : s ∈ Icc 0 t) : s ∈ Ico 0 S := ⟨hs.1, hs.2.trans_lt htS⟩
  have hcommon (s) (hs : s ∈ Icc 0 t) : s ∈ Ico 0 F.lifetime ∩ Ico 0 F'.lifetime :=
    ⟨⟨hs.1, hs.2.trans_lt ht.1.2⟩, ⟨hs.1, hs.2.trans_lt ht.2.2⟩⟩
  have hinterior (s) (hs : s ∈ Ioo 0 t) :
      s ∈ interior (Ico 0 F.lifetime ∩ Ico 0 F'.lifetime) := by
    rw [interior_inter, interior_Ico, interior_Ico]
    exact ⟨⟨hs.1, hs.2.trans ht.1.2⟩, ⟨hs.1, hs.2.trans ht.2.2⟩⟩
  have hr (i a b c : ℕ) (s : ℝ) (hs : s ∈ Ioo 0 t)
      (hD : D i s ≤ C * (E a s + E b s + E c s)) :
      deriv (E i) s ≤ (L * C) * (E a s + E b s + E c s) := by
    calc
      _ ≤ L * D i s := hrate i s (hclosed s ⟨hs.1.le, hs.2.le⟩) (hinterior s hs)
      _ ≤ L * (C * (E a s + E b s + E c s)) := mul_le_mul_of_nonneg_left hD hL
      _ = _ := (mul_assoc _ _ _).symm
  have hzero : ∀ i, EqOn (E i) (fun _ => 0) (Icc 0 t) :=
    eq_zero_of_uniformly_bounded_neighbor_energy_rates (mul_nonneg hL hC)
      (fun i => capDifferenceEnergy_continuousOn e qH qA qS F.flow F'.flow p
        isCompact_Icc (fun s hs => hcommon s hs) i)
      (fun i s hs => capDifferenceEnergy_differentiableAt e qH qA qS F.flow F'.flow p
        (hinterior s hs) i)
      (fun i => capDifferenceEnergy_eq_zero_of_metric_eq e qH qA qS F.flow F'.flow p
        (F.initial_metric.trans F'.initial_metric.symm) i)
      (fun i s _ => capDifferenceEnergy_nonneg e qH qA qS F.flow F'.flow p i s)
      (fun i s hs => hvalue i s (hclosed s hs))
      (fun s hs => hr 0 0 1 2 s hs
        (hsupport F.flow F'.flow p (hcommon s ⟨hs.1.le, hs.2.le⟩)).1)
      (fun s hs => hr 1 0 1 2 s hs
        (hsupport F.flow F'.flow p (hcommon s ⟨hs.1.le, hs.2.le⟩)).2.1)
      (fun j s hs => hr (j + 2) (j + 1) (j + 2) (j + 3) s hs
        ((hsupport F.flow F'.flow p (hcommon s ⟨hs.1.le, hs.2.le⟩)).2.2 j))
  exact metric_eq_of_capDifferenceEnergy_zero e qH qA qS F.flow F'.flow p ht
    (fun i => hzero i ⟨ht.1.1, le_rfl⟩)

end PoincareConjecture.M34

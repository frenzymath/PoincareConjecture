import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderBounds
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderEnergy
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackBounds
import PoincareConjecture.Proofs.M34.Standard.UniformFamilyEnergyBounds
import PoincareConjecture.Proofs.M34.Mathlib.BoundedBoundaryEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open DifferenceEnergy

variable (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
  (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
  (e : StandardCylindricalEnd g0.metric)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (p : endReferenceRegion e)

include P E0

theorem partialFlow_endCylinderDifferenceEnergy_bounds {T : ℝ}
    (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) :
    let E := endCylinderDifferenceEnergy e qH qA qS F.flow p
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧
      (∀ i t, t ∈ Icc 0 T → E i t ≤ M) ∧
      (∀ j t, t ∈ Ioo 0 T →
        deriv (E (j + 1)) t ≤ C * (E j t + E (j + 1) t + E (j + 2) t)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  intro E
  obtain ⟨S, hTS, hSF⟩ := exists_between hT.1.2
  have hS : 0 < S := hT.1.1.trans_lt hTS
  obtain ⟨B0, _hB0, hb0⟩ := F.curvature_locally_bounded S hS.le hSF
  let B := max 1 B0
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hfull (s) (hs : s ∈ Ico 0 S) (x) : (F.flow.connection s).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans ((hb0 s ⟨hs.1, hs.2.le⟩ x).trans (le_max_right _ _))
  obtain ⟨aA, MA, haA, _hMA, hA⟩ := partialFlow_endPullback_bounds P E0 F e
    hS hSF.le hB hfull (energyCutoffs_hasCompactSupport e).1 3
  obtain ⟨aB, MB, haB, _hMB, hBmodel⟩ := endCylinderFlow_compact_bounds e hT.2.2
    (energyCutoffs_hasCompactSupport e).1 3
  obtain ⟨M, L, hM, hL, hfamily⟩ := exists_uniformFamily_energy_bounds
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
    ((energyCutoffs_contDiff e).1.of_le (by simp)) (energyCutoffs_hasCompactSupport e).1
    (endEnergyCutoff_tsupport_subset_region e) haA haB MA MB
  have hj (j : ℕ) : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hclosed (t) (ht : t ∈ Icc 0 T) : t ∈ Ico 0 S := ⟨ht.1, ht.2.trans_lt hTS⟩
  have hcommon (t) (ht : t ∈ Icc 0 T) : t ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨⟨ht.1, ht.2.trans_lt hT.1.2⟩, ⟨ht.1, ht.2.trans_lt hT.2.2⟩⟩
  have hinterior (t) (ht : t ∈ Ioo 0 T) : t ∈ interior (Ico 0 F.lifetime ∩ Ico 0 1) := by
    rw [interior_inter, interior_Ico, interior_Ico]
    exact ⟨⟨ht.1, ht.2.trans hT.1.2⟩, ⟨ht.1, ht.2.trans hT.2.2⟩⟩
  obtain ⟨hvalue, hrate⟩ := hfamily (K := Icc 0 T)
    (fun j : ℕ => endPullbackFlow e F.flow j (hj j)) (fun _ : ℕ => endCylinderFlow e) p
    (fun j t ht x hx => hA j (hj j) t (hclosed t ht) p x hx
      (endEnergyCutoff_tsupport_subset_region e hx))
    (fun _ t ht x hx => hBmodel t ht p x hx (endEnergyCutoff_tsupport_subset_region e hx))
  obtain ⟨C, hC, hsupport⟩ := exists_endCylinderDifferenceSupportIntegral_bound e qH qA qS
  refine ⟨M, L * C, hM, mul_nonneg hL hC,
    fun i t ht => hvalue i t ht (hcommon t ht), ?_⟩
  intro j t ht
  let D := endCylinderDifferenceSupportIntegral e qH qA qS F.flow p
  calc
    _ ≤ L * D (j + 1) t := hrate (j + 1) t ⟨ht.1.le, ht.2.le⟩ (hinterior t ht)
    _ ≤ L * (C * (E j t + E (j + 1) t + E (j + 2) t)) :=
      mul_le_mul_of_nonneg_left
        (hsupport F.flow p (hcommon t ⟨ht.1.le, ht.2.le⟩) j) hL
    _ = _ := (mul_assoc _ _ _).symm

theorem partialFlow_endCylinderDifferenceEnergy_decay {T : ℝ}
    (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ ∀ j t, t ∈ Icc 0 T →
      endCylinderDifferenceEnergy e qH qA qS F.flow p (j + 1) t ≤
        M * (1 / 2 : ℝ) ^ (j + 1) * Real.exp (9 * C * t) := by
  obtain ⟨M, C, hM, hC, hvalue, hrate⟩ :=
    partialFlow_endCylinderDifferenceEnergy_bounds P E0 F e qH qA qS p hT
  have hcommon (t) (ht : t ∈ Icc 0 T) : t ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨⟨ht.1, ht.2.trans_lt hT.1.2⟩, ⟨ht.1, ht.2.trans_lt hT.2.2⟩⟩
  have hinterior (t) (ht : t ∈ Ioo 0 T) : t ∈ interior (Ico 0 F.lifetime ∩ Ico 0 1) := by
    rw [interior_inter, interior_Ico, interior_Ico]
    exact ⟨⟨ht.1, ht.2.trans hT.1.2⟩, ⟨ht.1, ht.2.trans hT.2.2⟩⟩
  have hdecay := le_geometric_exp_of_bounded_boundary_energy hC
    (fun j => endCylinderDifferenceEnergy_continuousOn e qH qA qS F.flow p
      isCompact_Icc (fun t ht => hcommon t ht) (j + 1))
    (fun j t ht => endCylinderDifferenceEnergy_differentiableAt e qH qA qS F.flow p
      (hinterior t ht) (j + 1))
    (fun j => endCylinderDifferenceEnergy_zero e qH qA qS F.flow p F.initial_metric (j + 1))
    (fun j t _ => endCylinderDifferenceEnergy_nonneg e qH qA qS F.flow p (j + 1) t)
    hvalue hrate
  refine ⟨M, C, hM, hC, ?_⟩
  simpa only [sub_zero] using hdecay

theorem partialFlow_endCylinderDifferenceEnergy_tendstoUniformlyOn {T : ℝ}
    (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) :
    TendstoUniformlyOn
      (fun j => endCylinderDifferenceEnergy e qH qA qS F.flow p (j + 1))
      (fun _ => 0) atTop (Icc 0 T) := by
  obtain ⟨M, C, hM, hC, hbound⟩ :=
    partialFlow_endCylinderDifferenceEnergy_decay P E0 F e qH qA qS p hT
  have hp : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
  have hsmall : Tendsto (fun j : ℕ => M * (1 / 2 : ℝ) ^ (j + 1) * Real.exp (9 * C * T))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hp.const_mul M).mul_const (Real.exp (9 * C * T))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj
  intro t ht
  rw [dist_comm, dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (endCylinderDifferenceEnergy_nonneg e qH qA qS F.flow p (j + 1) t)]
  apply (hbound j t ht).trans_lt
  apply lt_of_le_of_lt _ hj
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) hC)))
    (mul_nonneg hM (pow_nonneg (by norm_num) _))

end PoincareConjecture.M34

import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Energy.CutoffL2SpatialJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderDifference
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndSlabCover

/-!
# Spatial-jet decay of the actual end-cylinder difference

The proved compact-cutoff L2 energy of the native coefficient
difference decays uniformly on a closed common time horizon. The
generic cutoff-to-jet comparison therefore sends every spatial jet to
zero, uniformly on the cutoff plateau slab. This is Proposition 12.7,
pp. 298-299 and cutoff-l2-spatial-jets.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

variable (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
  (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
  (e : StandardCylindricalEnd g0.metric)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (p : endReferenceRegion e)

include P E0 qH qA qS p

/-- Finite-coordinate cutoff energy of the native end-cylinder difference
vanishes uniformly on a closed common horizon
(Proposition 12.7, pp. 298-299). -/
theorem partialFlow_endCylinder_cutoffCoordinateEnergy_tendstoUniformlyOn {T : ℝ}
    (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) :
    TendstoUniformlyOn
      (fun j t => cutoffCoordinateEnergy (qH : FH 3 →L[ℝ] EuclideanSpace ℝ (Fin dH))
        (endEnergyCutoff e) (endCylinderDifferenceCoefficients e F.flow (j + 1) t))
      (fun _ => 0) atTop (Icc 0 T) := by
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  have hE :=
    partialFlow_endCylinderDifferenceEnergy_tendstoUniformlyOn P E0 F e qH qA qS p hT
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hE) ε hε] with j hj t ht
  have hnn := cutoffCoordinateEnergy_nonneg
    (qH : FH 3 →L[ℝ] EuclideanSpace ℝ (Fin dH)) (endEnergyCutoff e)
    (endCylinderDifferenceCoefficients e F.flow (j + 1) t)
  have htJ : t ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨⟨ht.1, ht.2.trans_lt hT.1.2⟩, ⟨ht.1, ht.2.trans_lt hT.2.2⟩⟩
  have hle :
      cutoffCoordinateEnergy (qH : FH 3 →L[ℝ] EuclideanSpace ℝ (Fin dH))
          (endEnergyCutoff e)
          (endCylinderDifferenceCoefficients e F.flow (j + 1) t) ≤
        endCylinderDifferenceEnergy e qH qA qS F.flow p (j + 1) t := by
    simpa [cutoffCoordinateEnergy] using
      endCylinderDifferenceCoefficients_energy_le e qH qA qS F.flow p htJ (j + 1)
  have hEd : endCylinderDifferenceEnergy e qH qA qS F.flow p (j + 1) t < ε := by
    have := hj t ht
    rwa [dist_comm, dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (endCylinderDifferenceEnergy_nonneg e qH qA qS F.flow p (j + 1) t)]
      at this
  rw [dist_comm, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle.trans_lt hEd

/-- Every spatial jet of the native end-cylinder difference vanishes
uniformly on the cutoff plateau, before the translation index and
included time (Proposition 12.7, pp. 298-299). -/
theorem partialFlow_endCylinderDifferenceCoefficients_iteratedFDeriv_tendsto
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ k ≥ N, ∀ t ∈ Icc 0 T,
      ∀ x ∈ endClosedSlab e (17 / 5) (23 / 5),
        ‖iteratedFDeriv ℝ m
          (endCylinderDifferenceCoefficients e F.flow (k + 1) t) x‖ < ε := by
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  let U := endReferenceRegion e
  have hU : IsOpen U := endReferenceRegion_isOpen e
  have hφ := (energyCutoffs_contDiff e).1.continuous
  have hφc := (energyCutoffs_hasCompactSupport e).1
  have hφU := endEnergyCutoff_tsupport_subset_region e
  have hK : IsCompact (endClosedSlab e (17 / 5) (23 / 5)) :=
    endClosedSlab_isCompact e (by norm_num)
  have hKφ : endClosedSlab e (17 / 5) (23 / 5) ⊆ {y | endEnergyCutoff e y ≠ 0} := by
    intro y hy
    have hy1 : endEnergyCutoff e y = 1 := endEnergyCutoff_eq_one_on_slab (e := e) hy
    simp [hy1]
  have hf : ∀ k t, t ∈ Icc (0 : ℝ) T →
      ContDiffOn ℝ ∞ (endCylinderDifferenceCoefficients e F.flow (k + 1) t) U :=
    fun k t _ => endCylinderDifferenceCoefficients_contDiffOn e F.flow (k + 1) t
  have hbound : ∀ K, IsCompact K → K ⊆ U → ∀ m' : ℕ, ∃ M : ℝ,
      ∀ k t, t ∈ Icc (0 : ℝ) T → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m' (endCylinderDifferenceCoefficients e F.flow (k + 1) t) x‖ ≤ M := by
    intro K hKc hKU m'
    obtain ⟨M, hM⟩ :=
      partialFlow_endCylinderDifferenceCoefficients_bounds P E0 F e hT hKc m'
    refine ⟨M, fun k t ht x hx => hM (k + 1) t ht x hx (hKU hx)⟩
  have hL :=
    partialFlow_endCylinder_cutoffCoordinateEnergy_tendstoUniformlyOn
      P E0 F e qH qA qS p hT
  exact tendstoUniformlyOn_iteratedFDeriv_of_cutoff_energy_Icc hU
    (qH : FH 3 →L[ℝ] EuclideanSpace ℝ (Fin dH)) qH.injective
    hφ hφc hφU hf hbound hL m hK hKφ ε hε

end PoincareMT.M34

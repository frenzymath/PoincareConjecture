import PoincareConjecture.Proofs.M47.SeedLimitContractedTest
import PoincareConjecture.Proofs.M47.LimitNoncollapseVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

theorem seedLimit_noncollapsed_of_buffered_physical_volume
    (P : M47Predecessors.{u})
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
    (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
    (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
    (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
    (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
    (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)
    {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
      (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
      (blowupBackwardInterval H))
    {a w epsilon kappa : ℝ} (hw : 0 < w) (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hbase : ∀ k, a ≤ baseTime k)
    (hcutoff : ∀ k, epsilon ≤ (F k).parameters.epsilon)
    (hvolume : ∀ᶠ k in atTop,
      SurgeryVolumeControlOn (F k) (Icc (a - w) (baseTime k)) kappa (fun _ _ => True)) :
    BlowupLimitNoncollapsed G.limit kappa := by
  classical
  dsimp only [BlowupLimitNoncollapsed]
  let : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
  let : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
  let : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
    G.limit.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  intro t ht p r hr htime hcurv
  apply limitNoncollapse_exact_density_of_theta_bounds
  intro theta htheta
  let rho := theta ^ 2 * r
  let sigma := theta * r
  let lambda := (1 + theta) / 2
  have hrho : 0 < rho := mul_pos (sq_pos_of_pos htheta.1) hr
  have hsigma : 0 < sigma := mul_pos htheta.1 hr
  have hlambda : 0 < lambda := by dsimp [lambda]; linarith [htheta.1]
  have hlambda_lt : lambda < 1 := by dsimp [lambda]; linarith [htheta.2]
  have htheta_lambda : theta < lambda := by dsimp [lambda]; linarith [htheta.2]
  have hrho_sigma : rho < sigma := by
    apply mul_lt_mul_of_pos_right _ hr
    nlinarith [htheta.1, htheta.2]
  have hsigma_r : sigma < r := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta.2 hr
  have hgap : rho / lambda < sigma := by
    apply (div_lt_iff₀ hlambda).mpr
    have h := mul_lt_mul_of_pos_right htheta_lambda hsigma
    dsimp [rho, sigma] at h ⊢
    nlinarith
  obtain ⟨R, hbuffer, hRsigma⟩ := exists_between hgap
  have hR : 0 < R := (div_pos hrho hlambda).trans hbuffer
  have hv := seedLimit_contracted_physical_test_volume F W history baseTime hbaseTime
    basePoint hPositive hDiverges G P hw hepsilon hbase hcutoff hvolume t ht p
    hr hrho (hrho_sigma.trans hsigma_r) hR (hRsigma.trans hsigma_r)
    hlambda hlambda_lt hbuffer htime hcurv
  have hpower : theta ^ 3 ≤ lambda ^ 3 :=
    pow_le_pow_left₀ htheta.1.le htheta_lambda.le 3
  have hdensity : kappa * theta ^ 9 * r ^ 3 ≤ kappa * lambda ^ 3 * rho ^ 3 := by
    calc
      _ = kappa * theta ^ 3 * rho ^ 3 := by dsimp [rho]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hkappa.le) (pow_nonneg hrho.le 3)
  exact (ENNReal.ofReal_le_ofReal hdensity).trans hv

end PoincareConjecture.Proofs.M47

import PoincareConjecture.Proofs.M32.Claim11_35.ScalarLaplacianJets
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M32

open PoincareConjecture.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

attribute [local instance] scalarCoefficientNormedGroup scalarCoefficientNormedSpace
  scalarTwoJetNormedGroup scalarTwoJetNormedSpace
  scalarTwoJetFirstNormedGroup scalarTwoJetFirstNormedSpace
  scalarTwoJetSecondNormedGroup scalarTwoJetSecondNormedSpace
  scalarFourJetNormedGroup scalarFourJetNormedSpace

private theorem norm_iteratedFDeriv_metricTwoJet_le {n m : ℕ}
    {B : E n → MetricCoefficient n} {x : E n} (hB : ContDiffAt ℝ ∞ B x)
    {c : ℝ} (hbound : ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j B x‖ ≤ c) :
    ‖iteratedFDeriv ℝ m (metricTwoJet B) x‖ ≤ c := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  have hB'' := hB'.fderiv_right (m := ∞) (by simp)
  change ‖iteratedFDeriv ℝ m (fun y => (B y, fderiv ℝ B y,
    fderiv ℝ (fderiv ℝ B) y)) x‖ ≤ c
  rw [iteratedFDeriv_prodMk hB (hB'.prodMk hB'') (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le (hbound m (by omega))
  rw [iteratedFDeriv_prodMk hB' hB'' (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod,
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  exact max_le (hbound (m + 1) (by omega)) (hbound (m + 1 + 1) (by omega))

set_option maxHeartbeats 800000 in

private theorem norm_scalarMetricFourJet_le {n : ℕ}
    {B : E n → MetricCoefficient n} {x : E n} (hB : ContDiffAt ℝ ∞ B x)
    {c : ℝ} (hbound : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j B x‖ ≤ c) :
    ‖scalarMetricFourJet B x‖ ≤ c := by
  have hJ (m : ℕ) (hm : m ≤ 2) : ‖iteratedFDeriv ℝ m (metricTwoJet B) x‖ ≤ c :=
    norm_iteratedFDeriv_metricTwoJet_le hB (fun j hj => hbound j (by omega))
  have hzero := hJ 0 (by omega)
  have hone := hJ 1 (by omega)
  have htwo := hJ 2 le_rfl
  rw [norm_iteratedFDeriv_zero] at hzero
  rw [norm_iteratedFDeriv_one] at hone
  have hsecond : ‖fderiv ℝ (fderiv ℝ (metricTwoJet B)) x‖ =
      ‖iteratedFDeriv ℝ 2 (metricTwoJet B) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  change max ‖metricTwoJet B x‖
    (max ‖fderiv ℝ (metricTwoJet B) x‖ ‖fderiv ℝ (fderiv ℝ (metricTwoJet B)) x‖) ≤ c
  exact max_le hzero (max_le hone (hsecond.le.trans htwo))

private theorem metricTwoJet_sub_of_contDiff {n : ℕ}
    {B C : E n → MetricCoefficient n} (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) :
    metricTwoJet (B - C) = metricTwoJet B - metricTwoJet C := by
  funext y
  exact secondDerivativeTriple_sub hB hC y

set_option maxHeartbeats 800000 in

private theorem scalarMetricFourJet_sub_of_contDiff {n : ℕ}
    {B C : E n → MetricCoefficient n} (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (x : E n) :
    scalarMetricFourJet (B - C) x = scalarMetricFourJet B x - scalarMetricFourJet C x := by
  have hJB : ContDiff ℝ ∞ (metricTwoJet B) :=
    contDiff_iff_contDiffAt.mpr fun y => contDiffAt_metricTwoJet (hB.contDiffAt (x := y))
  have hJC : ContDiff ℝ ∞ (metricTwoJet C) :=
    contDiff_iff_contDiffAt.mpr fun y => contDiffAt_metricTwoJet (hC.contDiffAt (x := y))
  unfold scalarMetricFourJet
  rw [metricTwoJet_sub_of_contDiff hB hC]
  exact secondDerivativeTriple_sub hJB hJC x

set_option maxHeartbeats 800000 in

private theorem norm_scalarMetricFourJet_sub_le {n : ℕ}
    {B C : E n → MetricCoefficient n} (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (x : E n) {c : ℝ}
    (hbound : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j B x - iteratedFDeriv ℝ j C x‖ ≤ c) :
    ‖scalarMetricFourJet B x - scalarMetricFourJet C x‖ ≤ c := by
  rw [← scalarMetricFourJet_sub_of_contDiff hB hC]
  apply norm_scalarMetricFourJet_le (hB.sub hC).contDiffAt
  intro j hj
  change ‖iteratedFDeriv ℝ j (B - C) x‖ ≤ c
  rw [iteratedFDeriv_sub_apply (i := j) (x := x)
    (hB.contDiffAt.of_le (by exact_mod_cast le_top))
    (hC.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact hbound j hj

set_option maxHeartbeats 800000 in




theorem exists_scalar_laplacian_control_of_metric_fourJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (h : RiemannianMetric n (E n)) (D' : LeviCivitaData h),
      (∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j h.euclideanCoefficients x -
        iteratedFDeriv ℝ j g.euclideanCoefficients x‖ < delta) →
      |D'.laplacian D'.scalarCurvature x - D.laplacian D.scalarCurvature x| < alpha := by
  have hc := continuousAt_scalarLaplacianFourJet
    (K := scalarMetricFourJet g.euclideanCoefficients x) (g.inner_isInvertible x)
  obtain ⟨eta, heta, hclose⟩ := Metric.continuousAt_iff.mp hc alpha halpha
  refine ⟨eta / 2, half_pos heta, ?_⟩
  intro h D' hjets
  have hdist : dist (scalarMetricFourJet h.euclideanCoefficients x)
      (scalarMetricFourJet g.euclideanCoefficients x) < eta := by
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (norm_scalarMetricFourJet_sub_le
      (contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients)
      (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients) x
      (fun j hj => (hjets j hj).le))
    exact half_lt_self heta
  have hresult := hclose hdist
  rw [scalarLaplacianFourJet_scalarMetricFourJet D' x,
    scalarLaplacianFourJet_scalarMetricFourJet D x, Real.dist_eq] at hresult
  exact hresult




theorem tendsto_scalar_laplacian_of_metric_fourJet {n : ℕ} {ι : Type*} {l : Filter ι}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g)
    (h : ι → RiemannianMetric n (E n)) (D' : ∀ a, LeviCivitaData (h a)) (x : E n)
    (hjets : ∀ j : ℕ, j ≤ 4 → Tendsto
      (fun a => iteratedFDeriv ℝ j (h a).euclideanCoefficients x) l
      (𝓝 (iteratedFDeriv ℝ j g.euclideanCoefficients x))) :
    Tendsto (fun a => (D' a).laplacian (D' a).scalarCurvature x) l
      (𝓝 (D.laplacian D.scalarCurvature x)) := by
  apply Metric.tendsto_nhds.mpr
  intro alpha halpha
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_scalar_laplacian_control_of_metric_fourJet D x halpha
  have hevent (j : Fin 5) : ∀ᶠ a in l,
      ‖iteratedFDeriv ℝ j.val (h a).euclideanCoefficients x -
        iteratedFDeriv ℝ j.val g.euclideanCoefficients x‖ < delta := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp
      (hjets j.val (by omega)) delta hdelta
  filter_upwards [Filter.eventually_all.mpr hevent] with a ha
  simpa only [Real.dist_eq] using hcontrol (h a) (D' a)
    (fun j hj => ha (⟨j, by omega⟩ : Fin 5))

end PoincareConjecture.M32

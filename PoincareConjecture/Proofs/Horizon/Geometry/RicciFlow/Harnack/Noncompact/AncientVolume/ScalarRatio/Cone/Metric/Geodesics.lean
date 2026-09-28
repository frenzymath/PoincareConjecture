import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.BallApproximation
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.Curves.Midpoints












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace Poincare.AncientVolume.ScalarRatio

private theorem exact_split_of_compact_approximation
    {Y : Type*} [MetricSpace Y] {K : Set Y} (hK : IsCompact K)
    {x y : Y} (hx : x ∈ K) (r : ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K,
      dist x z < r + ε ∧ dist z y < dist x y - r + ε) :
    ∃ z : Y, dist x z = r ∧ dist z y = dist x y - r := by
  let f : Y → ℝ := fun z => max (dist x z - r) (dist z y - (dist x y - r))
  have hf : Continuous f :=
    ((continuous_const.dist continuous_id).sub continuous_const).max
      ((continuous_id.dist continuous_const).sub continuous_const)
  obtain ⟨z, _, hz⟩ := hK.exists_isMinOn ⟨x, hx⟩ hf.continuousOn
  have hz0 : f z ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, hw, hw₁, hw₂⟩ := happrox ε hε
    have hfw : f w < ε := max_lt (by linarith) (by linarith)
    simpa only [zero_add] using (hz hw).trans hfw.le
  have h₁ := (le_max_left (dist x z - r) (dist z y - (dist x y - r))).trans hz0
  have h₂ := (le_max_right (dist x z - r) (dist z y - (dist x y - r))).trans hz0
  have htri := dist_triangle x z y
  exact ⟨z, by linarith, by linarith⟩

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem source_metric_split
    (g : RiemannianMetric n M) (hc : MetricComplete g) :
    letI := g.toMetricSpace
    ∀ (x y : M) (r : ℝ), 0 ≤ r → r ≤ dist x y →
      ∃ z : M, dist x z = r ∧ dist z y = dist x y - r := by
  let := g.toMetricSpace
  intro x y r hr hry
  rcases hr.eq_or_lt with hr | hr
  · exact ⟨x, by simp [← hr], by simp [← hr]⟩
  have hd : 0 < dist x y := hr.trans_le hry
  obtain ⟨ε, _, γ, _, hγ0, hγ1, hγ⟩ := g.exists_minimizing_geodesic_of_metricComplete hc x y
  have hdist (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (γ s) (γ t) = |s - t| * dist x y := by
    change (g.edist (γ s) (γ t)).toReal = |s - t| * (g.edist x y).toReal
    rw [hγ s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  let t := r / dist x y
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.le hd.le, (div_le_one hd).mpr hry⟩
  refine ⟨γ t, ?_, ?_⟩
  · have hh := hdist 0 (by simp) t ht
    simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1, t, div_mul_cancel₀ _ hd.ne'] using hh
  · have hh := hdist t ht 1 (by simp)
    rw [hγ1, abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub, sub_mul, one_mul,
      show t * dist x y = r from div_mul_cancel₀ r hd.ne'] at hh
    exact hh



theorem asymptoticCone_exists_distance_split [NoncompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∀ (x y : AsymptoticCone p hcomparison) (r : ℝ), 0 ≤ r → r ≤ dist x y →
      ∃ z : AsymptoticCone p hcomparison, dist x z = r ∧ dist z y = dist x y - r := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
  dsimp only
  intro x y r hr hry
  rcases hr.eq_or_lt with hr | hr
  · exact ⟨x, by simp [← hr], by simp [← hr]⟩
  rcases hry.eq_or_lt with hry | hry
  · exact ⟨y, hry.symm, by simp [hry]⟩
  let R := (asymptoticConeRadius hcomparison x : ℝ) +
    asymptoticConeRadius hcomparison y + dist x y + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hxK : x ∈ asymptoticConeClosedAnnulus hcomparison 0 R := by
    constructor
    · exact (asymptoticConeRadius hcomparison x).coe_nonneg
    · dsimp only [R]
      linarith [(asymptoticConeRadius hcomparison y).coe_nonneg, dist_nonneg (x := x) (y := y)]
  have hyK : y ∈ asymptoticConeClosedAnnulus hcomparison 0 R := by
    constructor
    · exact (asymptoticConeRadius hcomparison y).coe_nonneg
    · dsimp only [R]
      linarith [(asymptoticConeRadius hcomparison x).coe_nonneg, dist_nonneg (x := x) (y := y)]
  apply exact_split_of_compact_approximation
    (isCompact_asymptoticConeClosedAnnulus hcomparison 0 R) hxK r
  intro ε hε
  let δ := min (ε / 4) ((dist x y - r) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδr : δ ≤ (dist x y - r) / 4 := min_le_right _ _
  obtain ⟨L, hL, happrox⟩ := g.exists_closedBallConeRelation_approximation_of_metricComplete
    D hc hsec p hR hδ
  obtain ⟨hforward, hback, hrad, herr⟩ := happrox L le_rfl
  obtain ⟨a, ha⟩ := hback ⟨x, hxK⟩
  obtain ⟨b, hb⟩ := hback ⟨y, hyK⟩
  have hab := abs_lt.mp (herr a b ⟨x, hxK⟩ ⟨y, hyK⟩ ha hb)
  change -δ < dist (a : M) (b : M) / L - dist x y ∧
    dist (a : M) (b : M) / L - dist x y < δ at hab
  have hrab : r < dist (a : M) (b : M) / L := by linarith
  obtain ⟨c, hac, hcb⟩ := g.source_metric_split hc (a : M) (b : M) (r * L)
    (mul_nonneg hr.le hL.le) ((lt_div_iff₀ hL).mp hrab).le
  have haR := hrad a ⟨x, hxK⟩ ha
  change (asymptoticConeRadius hcomparison x : ℝ) = dist p (a : M) / L at haR
  have hcR : dist p c / L ≤ R := by
    have hh := div_le_div_of_nonneg_right (dist_triangle p (a : M) c) hL.le
    rw [add_div, hac, mul_div_cancel_right₀ _ hL.ne', ← haR] at hh
    have hypos := (asymptoticConeRadius hcomparison y).coe_nonneg
    dsimp only [R]
    linarith
  let c' : rescaledClosedAnnulus p L 0 R := ⟨c, div_nonneg dist_nonneg hL.le, hcR⟩
  obtain ⟨z, hz⟩ := hforward c'
  have haz := (abs_lt.mp (herr a c' ⟨x, hxK⟩ z ha hz)).1
  have hzb := (abs_lt.mp (herr c' b z ⟨y, hyK⟩ hz hb)).1
  change -δ < dist (a : M) c / L - dist x (z : AsymptoticCone p hcomparison) at haz
  change -δ < dist c (b : M) / L - dist (z : AsymptoticCone p hcomparison) y at hzb
  rw [hac, mul_div_cancel_right₀ _ hL.ne'] at haz
  rw [hcb, sub_div, mul_div_cancel_right₀ _ hL.ne'] at hzb
  exact ⟨z, z.property, by linarith, by linarith⟩



theorem exists_asymptoticCone_metric_segment [NoncompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∀ x y : AsymptoticCone p hcomparison,
      ∃ γ : ℝ → AsymptoticCone p hcomparison, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  exact Poincare.MetricCurves.exists_metric_segment_of_splitting
    (g.asymptoticCone_exists_distance_split D hc hsec p)

end PoincareConjecture.RiemannianMetric

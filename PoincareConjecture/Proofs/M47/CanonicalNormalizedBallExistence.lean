import PoincareConjecture.Proofs.M34.Standard.CalibratedMetricComparison
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalizedBalls

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [CompactSpace M]

theorem exists_normalized_ball_on_compact (g : RiemannianMetric 3 M)
    {f : M → ℝ} (hf : Continuous f) (x : M) (hfx : 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (f x))⁻¹ ∧
      sSup (f '' g.ball x r) = r⁻¹ ^ 2 ∧ IsCompact (closure (g.ball x r)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := g.comparisonEMetric
  let V := Metric.eball x (⊤ : ℝ≥0∞)
  have hVclosed : IsClosed V := Metric.isClosed_eball_top
  have hVclopen : IsClopen V := ⟨hVclosed, Metric.isOpen_eball⟩
  let : CompactSpace V := isCompact_iff_compactSpace.mp hVclosed.isCompact
  have hfinite (y z : V) : edist y z ≠ ⊤ := by
    have hy : edist y.val x < ⊤ := y.property
    have hz : edist x z.val < ⊤ := by
      have h : edist z.val x < ⊤ := z.property
      simpa only [edist_comm] using h
    exact ne_of_lt ((edist_triangle y.val x z.val).trans_lt (ENNReal.add_lt_top.mpr ⟨hy, hz⟩))
  let : MetricSpace V := EMetricSpace.toMetricSpace hfinite
  let xV : V := ⟨x, Metric.mem_eball_self (by simp)⟩
  have hed (y z : V) : g.edist y.val z.val = ENNReal.ofReal (dist y z) :=
    edist_dist y z
  have hproject : ∀ R r eta : ℝ, 0 ≤ r → r ≤ R → 0 < eta →
      closedBall xV R ⊆ thickening (R - r + eta) (closedBall xV r) := by
    intro R r eta hr hrR heta y hy
    have hdelta : 0 < R - r + eta := by linarith
    by_cases hsmall : dist xV y ≤ r
    · apply Metric.mem_thickening_iff.mpr
      refine ⟨y, ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_comm] using hsmall
      · simpa only [dist_self] using hdelta
    have hrxy : r < dist xV y := lt_of_not_ge hsmall
    have hshort : Manifold.riemannianEDist (𝓡 3) x y.val <
        ENNReal.ofReal (dist xV y + eta) := by
      change g.edist xV.val y.val < _
      rw [hed]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := xV) (y := y)])).mpr
        (by linarith)
    obtain ⟨gamma, hgamma0, hgamma1, hgamma, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hshort
    have hpathComponent : gamma '' Icc (0 : ℝ) 1 ⊆ connectedComponent x :=
      (isPreconnected_Icc.image gamma hgamma.continuousOn).subset_connectedComponent
        ⟨0, by norm_num, hgamma0⟩
    have hgammaV (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : gamma s ∈ V :=
      hVclopen.connectedComponent_subset xV.property (hpathComponent ⟨s, hs, rfl⟩)
    have hcont : ContinuousOn (fun s => (g.edist x (gamma s)).toReal) (Icc (0 : ℝ) 1) := by
      intro s hs
      have hfin : edist x (gamma s) ≠ ⊤ := by
        have h := hgammaV s hs
        change edist (gamma s) x < ⊤ at h
        exact ne_of_lt (by simpa only [edist_comm] using h)
      have hd : ContinuousOn (fun v : ℝ => edist x (gamma v)) (Icc (0 : ℝ) 1) :=
        continuous_edist.comp_continuousOn (continuousOn_const.prodMk hgamma.continuousOn)
      exact ContinuousAt.comp_continuousWithinAt
        (f := fun v : ℝ => edist x (gamma v))
        (ENNReal.continuousAt_toReal hfin) (hd s hs)
    have hstart : (g.edist x (gamma 0)).toReal = 0 := by
      rw [hgamma0]
      change (edist x x).toReal = 0
      simp only [edist_self, ENNReal.toReal_zero]
    have hend : (g.edist x (gamma 1)).toReal = dist xV y := by
      rw [hgamma1, show x = xV.val from rfl, hed, ENNReal.toReal_ofReal dist_nonneg]
    have hrange : r ∈ Icc (g.edist x (gamma 0)).toReal (g.edist x (gamma 1)).toReal := by
      rw [hstart, hend]
      exact ⟨hr, hrxy.le⟩
    obtain ⟨s, hs, hdist⟩ := intermediate_value_Icc zero_le_one hcont hrange
    let z : V := ⟨gamma s, hgammaV s hs⟩
    have hdist' : dist xV z = r := hdist
    have hp := Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc le_rfl hs.2)) hgamma0 rfl hs.1
    have htail := Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc hs.1 le_rfl)) rfl hgamma1 hs.2
    change g.edist xV.val z.val ≤ _ at hp
    change g.edist z.val y.val ≤ _ at htail
    rw [hed, hdist'] at hp
    rw [hed] at htail
    have hsum : ENNReal.ofReal (r + dist z y) < ENNReal.ofReal (dist xV y + eta) := by
      rw [ENNReal.ofReal_add hr dist_nonneg]
      exact (add_le_add hp htail).trans_lt
        ((Manifold.pathELength_add hs.1 hs.2).trans_lt hlength)
    have hsum' : r + dist z y < dist xV y + eta :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := xV) (y := y)])).mp hsum
    apply Metric.mem_thickening_iff.mpr
    refine ⟨z, ?_, ?_⟩
    · change dist z xV ≤ r
      rw [dist_comm, hdist']
    · have hy' : dist xV y ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
      rw [dist_comm]
      linarith
  obtain ⟨r, hr, hrR, hnorm⟩ :=
    Metric.exists_pos_sSup_image_ball_eq_inv_sq_of_approximate_radial_projection xV
      hproject (hf.comp continuous_subtype_val) hfx
  have hball : Subtype.val '' Metric.ball xV r = g.ball x r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change g.edist xV.val z.val < ENNReal.ofReal r
      rw [hed]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by
        simpa only [Metric.mem_ball, dist_comm] using hz)
    · intro hy
      have hyV : y ∈ V := by
        change edist y x < ⊤
        rw [edist_comm]
        exact (show g.edist x y < ENNReal.ofReal r from hy).trans (ENNReal.ofReal_lt_top)
      refine ⟨⟨y, hyV⟩, ?_, rfl⟩
      have hy' : ENNReal.ofReal (dist xV ⟨y, hyV⟩) < ENNReal.ofReal r := by
        rw [← hed]
        exact hy
      simpa only [Metric.mem_ball, dist_comm] using (ENNReal.ofReal_lt_ofReal_iff hr).mp hy'
  have himages : (fun y : V => f y.val) '' Metric.ball xV r = f '' g.ball x r := by
    rw [← hball, image_image]
  exact ⟨r, hr, hrR, by rwa [← himages], isClosed_closure.isCompact⟩

theorem exists_scalar_normalized_ball_on_compact (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (x : M) (hR : 0 < D.scalarCurvature x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (D.scalarCurvature x))⁻¹ ∧
      scalarCurvatureSupOn g D (g.ball x r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (g.ball x r)) := by
  obtain ⟨r, hr, hrR, hnorm, hcompact⟩ := exists_normalized_ball_on_compact g
    (M34.contMDiff_scalarCurvature D).continuous x hR
  exact ⟨r, hr, hrR, by simpa only [scalarCurvatureSupOn, image_eq_range] using hnorm, hcompact⟩

end PoincareConjecture.Proofs.M47

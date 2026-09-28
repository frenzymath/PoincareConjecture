import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SmallNormalSphere
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricRayRegularity
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedCylinderMetricRays













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.M28

private theorem exists_fin_three_ne_pair
    {Y : Type*} (z : Fin 3 → Y) (hz : Function.Injective z) (x y : Y) :
    ∃ i, z i ≠ x ∧ z i ≠ y := by
  classical
  by_contra h
  have hvalues (i : Fin 3) : z i = x ∨ z i = y := by
    by_cases hix : z i = x
    · exact Or.inl hix
    · right
      by_contra hiy
      exact h ⟨i, hix, hiy⟩
  have h01 : z 0 ≠ z 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hz h)
  have h02 : z 0 ≠ z 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hz h)
  have h12 : z 1 ≠ z 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hz h)
  rcases hvalues 0 with h0 | h0 <;>
    rcases hvalues 1 with h1 | h1 <;>
    rcases hvalues 2 with h2 | h2
  all_goals first
    | exact h01 (h0.trans h1.symm)
    | exact h02 (h0.trans h2.symm)
    | exact h12 (h1.trans h2.symm)

private theorem continuousOn_of_unit_metric
    {Y : Type*} [MetricSpace Y] {S : Set ℝ} {gamma : ℝ → Y}
    (hmetric : ∀ s ∈ S, ∀ t ∈ S, dist (gamma s) (gamma t) = |s - t|) :
    ContinuousOn gamma S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hisometry : Isometry (fun t : S => gamma t.1) := by
    apply Isometry.of_dist_eq
    intro s t
    change dist (gamma s.1) (gamma t.1) = dist s.1 t.1
    simpa only [Real.dist_eq] using hmetric s.1 s.2 t.1 t.2
  exact hisometry.continuous

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem exists_point_off_intrinsic_metric_end_ray
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) {a : ℝ} {gamma : ℝ → U}, 0 < a →
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) →
      (∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma t : UniformSpace.Completion U) E = a - t) →
      ∃ q : U,
        a / 4 < dist (q : UniformSpace.Completion U) E ∧
        dist (q : UniformSpace.Completion U) E < 3 * a / 4 ∧
        q ∉ gamma '' Ico (0 : ℝ) a := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E a gamma ha hmetric hradius
  let gU := intrinsicOpenMetric g U
  have hmid : a / 2 ∈ Ico (0 : ℝ) a := ⟨(half_pos ha).le, half_lt_self ha⟩
  obtain ⟨delta, hdelta, hdeltaSmall, z, hz, hzedist⟩ :=
    gU.exists_three_points_at_small_edist (gamma (a / 2))
      (show 0 < a / 4 by positivity)
  have hedist (x y : U) : gU.edist x y = ENNReal.ofReal (dist x y) := by
    rw [intrinsicOpenMetric_edist, ← intrinsicOpenMetricSpace_edist g U hfinite,
      edist_dist]
  have hzdist (i : Fin 3) : dist (gamma (a / 2)) (z i) = delta := by
    have h := hzedist i
    rw [hedist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hdelta.le).mp h
  obtain ⟨i, hiLeft, hiRight⟩ := exists_fin_three_ne_pair z hz
    (gamma (a / 2 - delta)) (gamma (a / 2 + delta))
  have hoff : z i ∉ gamma '' Ico (0 : ℝ) a := by
    rintro ⟨t, ht, htz⟩
    have htabs : |a / 2 - t| = delta := by
      rw [← hmetric (a / 2) hmid t ht, htz]
      exact hzdist i
    rcases (abs_eq hdelta.le).mp htabs with hminus | hplus
    · have htime : t = a / 2 - delta := by linarith only [hminus]
      exact hiLeft (htz.symm.trans (congrArg gamma htime))
    · have htime : t = a / 2 + delta := by linarith only [hplus]
      exact hiRight (htz.symm.trans (congrArg gamma htime))
  have hradial := abs_dist_sub_le (z i : UniformSpace.Completion U)
    (gamma (a / 2) : UniformSpace.Completion U) E
  rw [UniformSpace.Completion.dist_eq, dist_comm (z i) (gamma (a / 2)),
    hzdist i, hradius (a / 2) hmid] at hradial
  obtain ⟨hlo, hhi⟩ := abs_le.mp hradial
  exact ⟨z i, by linarith only [hlo, hdeltaSmall],
    by linarith only [hhi, hdeltaSmall], hoff⟩





theorem intrinsic_metric_rays_differ_near_end
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ {a b : ℝ} {gamma mu : ℝ → U}, 0 < b → b < a →
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) →
      (∀ s ∈ Ico (0 : ℝ) b, ∀ t ∈ Ico (0 : ℝ) b,
        dist (mu s) (mu t) = |s - t|) →
      mu 0 ∉ gamma '' Ico (0 : ℝ) a →
      ∀ c : ℝ, 0 < c → ∃ s ∈ Ioo (0 : ℝ) (min c b),
        gamma (a - s) ≠ mu (b - s) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro a b gamma mu hb hba hgamma hmu hoff c hc
  let gU := intrinsicOpenMetric g U
  let G : ℝ → U := fun s => gamma (a - s)
  let H : ℝ → U := fun s => mu (b - s)
  have hgammaGeo := (intrinsic_metric_ray_regular g U hfinite hgamma).1
  have hmuGeo := (intrinsic_metric_ray_regular g U hfinite hmu).1
  have hG : gU.IsGeodesicOn G (Ioo (0 : ℝ) b) := by
    intro s hs
    have ht : a - s ∈ Ioo (0 : ℝ) a := by
      constructor <;> linarith only [hba, hs.1, hs.2]
    simpa only [G, neg_one_mul, neg_add_eq_sub] using
      hgammaGeo.comp_affine (-1) a s
        (by simpa only [Set.mem_preimage, neg_one_mul, neg_add_eq_sub] using ht)
  have hH : gU.IsGeodesicOn H (Ioo (0 : ℝ) b) := by
    intro s hs
    have ht : b - s ∈ Ioo (0 : ℝ) b := by
      constructor <;> linarith only [hs.1, hs.2]
    simpa only [H, neg_one_mul, neg_add_eq_sub] using
      hmuGeo.comp_affine (-1) b s
        (by simpa only [Set.mem_preimage, neg_one_mul, neg_add_eq_sub] using ht)
  by_contra hnone
  have heqSmall : EqOn G H (Ioo (0 : ℝ) (min c b)) := by
    intro s hs
    by_contra hne
    exact hnone ⟨s, hs, hne⟩
  have hmin : 0 < min c b := lt_min hc hb
  have htime : min c b / 2 ∈ Ioo (0 : ℝ) b :=
    ⟨half_pos hmin, (half_lt_self hmin).trans_le (min_le_right _ _)⟩
  have hnear : G =ᶠ[𝓝 (min c b / 2)] H := by
    filter_upwards [Ioo_mem_nhds (half_pos hmin) (half_lt_self hmin)] with s hs
    exact heqSmall hs
  have heq := hG.eqOn_of_eq_nhds hH (convex_Ioo (0 : ℝ) b).isPreconnected
    htime hnear
  have hgammaCont := continuousOn_of_unit_metric hgamma
  have hmuCont := continuousOn_of_unit_metric hmu
  have hGCont : ContinuousOn G (Icc (b / 2) b) :=
    hgammaCont.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith only [hba, hs.2], by linarith only [hb, hs.1]⟩)
  have hHCont : ContinuousOn H (Icc (b / 2) b) :=
    hmuCont.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨sub_nonneg.mpr hs.2, by linarith only [hb, hs.1]⟩)
  have heqInterior : EqOn G H (Ioo (b / 2) b) :=
    fun s hs => heq ⟨(half_pos hb).trans hs.1, hs.2⟩
  have heqClosed : EqOn G H (Icc (b / 2) b) :=
    heqInterior.of_subset_closure hGCont hHCont Ioo_subset_Icc_self (by
      rw [closure_Ioo (half_lt_self hb).ne])
  have hend := heqClosed (show b ∈ Icc (b / 2) b from
    ⟨(half_lt_self hb).le, le_rfl⟩)
  change gamma (a - b) = mu (b - b) at hend
  rw [sub_self] at hend
  exact hoff ⟨a - b, ⟨(sub_pos.mpr hba).le, sub_lt_self a hb⟩, hend⟩




theorem exists_two_distinct_selected_metric_end_rays
    {g : RiemannianMetric 3 M} {X : Set M}
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) →
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      (∀ p : U, r p < alpha → 0 < f p) →
      (∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
        gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
        (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
          dist (gamma s) (gamma t) = |s - t|) ∧
        (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
        ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (C.inverse (gamma t)).2) →
      ∃ p q : U, ∃ gamma mu : ℝ → U,
        0 < r p ∧ r p < alpha / 4 ∧ r p / 4 < r q ∧ r q < 3 * r p / 4 ∧
        (gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
          (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
            dist (gamma s) (gamma t) = |s - t|) ∧
          (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
          ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (C.inverse (gamma t)).2) ∧
        (mu 0 = q ∧ Isometry (fun t : Ico (0 : ℝ) (r q) => mu t.1) ∧
          (∀ s ∈ Ico (0 : ℝ) (r q), ∀ t ∈ Ico (0 : ℝ) (r q),
            dist (mu s) (mu t) = |s - t|) ∧
          (∀ t ∈ Ico (0 : ℝ) (r q), r (mu t) = r q - t) ∧
          ∀ t ∈ Ico (0 : ℝ) (r q), (3 / 4 : ℝ) ≤ (C.inverse (mu t)).2) ∧
        q ∉ gamma '' Ico (0 : ℝ) (r p) ∧
        ∀ c : ℝ, 0 < c → ∃ s ∈ Ioo (0 : ℝ) (min c (r q)),
          gamma (r p - s) ≠ mu (r q - s) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha houtside
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  dsimp only
  intro hbarrier hproducer
  have hpositive (x : U) : 0 < r x :=
    dist_pos.mpr fun hx => houtside ⟨x, hx⟩
  obtain ⟨p, hp⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt E
    (show 0 < alpha / 4 by positivity)
  have hpSmall : r p < alpha / 4 := by
    simpa only [r, dist_comm E (p : UniformSpace.Completion U)] using hp
  have hpPositive : 0 < r p := hpositive p
  have hpalpha : r p < alpha := by linarith only [hpSmall, halpha]
  obtain ⟨gamma, hgamma0, hgammaIsometry, hgammaMetric, hgammaRadius, hgammaLower⟩ :=
    hproducer p (hbarrier p hpalpha)
  obtain ⟨q, hqLower, hqUpper, hoff⟩ :=
    exists_point_off_intrinsic_metric_end_ray g U hfinite E hpPositive
      hgammaMetric hgammaRadius
  have hqPositive : 0 < r q := (by positivity : 0 < r p / 4).trans hqLower
  have hqp : r q < r p := by linarith only [hqUpper, hpPositive]
  have hqalpha : r q < alpha := hqp.trans hpalpha
  obtain ⟨mu, hmu0, hmuIsometry, hmuMetric, hmuRadius, hmuLower⟩ :=
    hproducer q (hbarrier q hqalpha)
  refine ⟨p, q, gamma, mu, hpPositive, hpSmall, hqLower, hqUpper,
    ⟨hgamma0, hgammaIsometry, hgammaMetric, hgammaRadius, hgammaLower⟩,
    ⟨hmu0, hmuIsometry, hmuMetric, hmuRadius, hmuLower⟩, hoff, ?_⟩
  apply intrinsic_metric_rays_differ_near_end g U hfinite hqPositive hqp
    hgammaMetric hmuMetric
  simpa only [hmu0] using hoff

end PoincareConjecture.M28

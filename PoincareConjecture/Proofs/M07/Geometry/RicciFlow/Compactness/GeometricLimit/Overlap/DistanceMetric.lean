import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Radius
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Coverage









set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)

noncomputable def quotientDistance : Quotient O.setoid → Quotient O.setoid → ℝ :=
  Quotient.lift₂ (fun a b : Σ i, X i => D a.1 b.1 (a.2, b.2)) (by
    intro a b a' b' ha hb
    have hab := (hrel a.1 a'.1 a.2 a'.2).mp ha
    have hbb := (hrel b.1 b'.1 b.2 b'.2).mp hb
    exact (eq_of_zero_right hD a.2 hbb).trans
      ((comm hD _ _ _ _).trans ((eq_of_zero_right hD b'.2 hab).trans
        (comm hD _ _ _ _))))

@[simp] theorem quotientDistance_include (i j : ι) (x : X i) (y : X j) :
    quotientDistance hD O hrel (O.include i x) (O.include j y) = D i j (x, y) := rfl

theorem quotientDistance_self (q : Quotient O.setoid) :
    quotientDistance hD O hrel q q = 0 := by
  induction q using Quotient.inductionOn with
  | h a => exact self hD a.1 a.2

theorem quotientDistance_comm (q r : Quotient O.setoid) :
    quotientDistance hD O hrel q r = quotientDistance hD O hrel r q := by
  induction q using Quotient.inductionOn with
  | h a =>
    induction r using Quotient.inductionOn with
    | h b => exact comm hD a.1 b.1 a.2 b.2

theorem quotientDistance_triangle (q r s : Quotient O.setoid) :
    quotientDistance hD O hrel q s ≤
      quotientDistance hD O hrel q r + quotientDistance hD O hrel r s := by
  induction q using Quotient.inductionOn with
  | h a =>
    induction r using Quotient.inductionOn with
    | h b =>
      induction s using Quotient.inductionOn with
      | h c => exact triangle hD a.1 b.1 c.1 a.2 b.2 c.2

theorem quotientDistance_eq_zero_iff (q r : Quotient O.setoid) :
    quotientDistance hD O hrel q r = 0 ↔ q = r := by
  induction q using Quotient.inductionOn with
  | h a =>
    induction r using Quotient.inductionOn with
    | h b =>
      exact ⟨fun h => Quotient.sound ((hrel a.1 b.1 a.2 b.2).mpr h),
        fun h => (hrel a.1 b.1 a.2 b.2).mp (Quotient.exact h)⟩

theorem quotientDistance_continuous_right (q : Quotient O.setoid) :
    Continuous (quotientDistance hD O hrel q) := by
  induction q using Quotient.inductionOn with
  | h a => exact (quotientRadius hD O hrel a.2).continuous

include hD hrel in
theorem include_mem_compact_image_of_distance_lt
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i j : ι} {x : X i} {y : X j} {r : ℝ} (hr : 0 < r)
    (hK : IsCompact (closedBall x r)) (hd : D i j (x, y) < c i * r) :
    O.include j y ∈ O.include i '' closedBall x r := by
  have himage : ∀ᶠ k in atTop, e k j y ∈ e k i '' closedBall x r := by
    filter_upwards [(hD i j x y).eventually (gt_mem_nhds hd)] with k hk
    apply image_mono ball_subset_closedBall
    apply ball_subset_image_of_lower_bound (hopen k i) hr hK
      (fun z => hlower k i z x) (hconn k _ _) (hc i)
    simpa only [mem_ball, dist_comm] using hk
  obtain ⟨z, hz, hzero⟩ := exists_zero_of_eventually_mem_image hD L he hK
    ⟨x, mem_closedBall_self hr.le⟩ himage
  exact ⟨z, hz, (Quotient.sound ((hrel j i y z).mpr hzero)).symm⟩

theorem isOpen_iff_quotientDistance
    [∀ i, LocallyCompactSpace (X i)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (S : Set (Quotient O.setoid)) :
    IsOpen S ↔ ∀ q ∈ S, ∃ ε > 0, ∀ z,
      quotientDistance hD O hrel q z < ε → z ∈ S := by
  constructor
  · intro hS q hq
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp
        (hS.preimage (O.include_isOpenEmbedding a.1).continuous) a.2 hq
      obtain ⟨R, hR, hK⟩ := exists_isCompact_closedBall a.2
      let s := min r R / 2
      have hs : 0 < s := half_pos (lt_min hr hR)
      have hsr : s < r := lt_of_lt_of_le (half_lt_self (lt_min hr hR)) (min_le_left _ _)
      have hsR : s ≤ R := (half_le_self (le_of_lt (lt_min hr hR))).trans (min_le_right _ _)
      refine ⟨c a.1 * s, mul_pos (hc a.1) hs, ?_⟩
      intro z hz
      induction z using Quotient.inductionOn with
      | h b =>
        obtain ⟨x, hx, heq⟩ := include_mem_compact_image_of_distance_lt hD O hrel L he
          c hc hlower hopen hconn hs
          (hK.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hsR)) hz
        change O.include b.1 b.2 ∈ S
        rw [← heq]
        exact hrS (lt_of_le_of_lt hx hsr)
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    obtain ⟨ε, hε, hsub⟩ := h q hq
    have hball : {z | quotientDistance hD O hrel q z < ε} ∈ 𝓝 q :=
      (isOpen_lt (quotientDistance_continuous_right hD O hrel q) continuous_const).mem_nhds
        (by simpa only [mem_ofPred_eq, quotientDistance_self] using hε)
    exact mem_of_superset hball hsub


@[instance_reducible] noncomputable def quotientMetricSpace
    [∀ i, LocallyCompactSpace (X i)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r)) :
    MetricSpace (Quotient O.setoid) :=
  MetricSpace.ofDistTopology (quotientDistance hD O hrel)
    (quotientDistance_self hD O hrel) (quotientDistance_comm hD O hrel)
    (quotientDistance_triangle hD O hrel)
    (isOpen_iff_quotientDistance hD O hrel L he c hc hlower hopen hconn)
    (fun q r => (quotientDistance_eq_zero_iff hD O hrel q r).mp)

theorem quotientMetricSpace_proper
    [∀ i, LocallyCompactSpace (X i)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ι, ∃ K : ∀ j, Set (X j),
      (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    letI := quotientMetricSpace hD O hrel L he c hc hlower hopen hconn
    ProperSpace (Quotient O.setoid) := by
  let := quotientMetricSpace hD O hrel L he c hc hlower hopen hconn
  have hcompact (r : ℝ) : IsCompact {q | quotientRadius hD O hrel p q ≤ r} := by
    let R := max r 0 + 1
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨s, K, hK, hcov⟩ := hcover R hR
    exact isCompact_radius_sublevel_of_source_ball_cover hD O hrel L he s K hK p
      (lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)) hcov
  constructor
  intro q r
  apply (hcompact (dist (O.include i₀ p) q + r)).of_isClosed_subset isClosed_closedBall
  intro z hz
  change dist (O.include i₀ p) z ≤ dist (O.include i₀ p) q + r
  have hz' : dist q z ≤ r := by simpa only [mem_closedBall, dist_comm] using hz
  exact (dist_triangle _ q _).trans (add_le_add le_rfl hz')

end PoincareConjecture.ChartDistance

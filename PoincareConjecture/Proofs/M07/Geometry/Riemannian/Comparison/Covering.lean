import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.FiniteCover
import PoincareConjecture.Proofs.M07.MeasureTheory.Measure.Packing











noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem ball_subset_ball_add (g : RiemannianMetric n M)
    {p x : M} {R r : ℝ} (hR : 0 ≤ R) (hx : x ∈ g.ball p R) (hr : 0 ≤ r) :
    g.ball x r ⊆ g.ball p (R + r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  change g.edist p y < ENNReal.ofReal (R + r)
  rw [ENNReal.ofReal_add hR hr]
  exact lt_of_le_of_lt Manifold.riemannianEDist_triangle (ENNReal.add_lt_add hx hy)


theorem volumeMeasure_ball_pos (g : RiemannianMetric n M) (p : M)
    {R : ℝ} (hR : 0 < R) : 0 < g.volumeMeasure (g.ball p R) := by
  obtain ⟨r, hbound, hr, hrR⟩ :=
    ((g.eventually_volumeMeasure_ball_bounds p (K := 2) (by norm_num)).and
      (Ioo_mem_nhdsGT hR)).exists
  have hpos : 0 < g.volumeMeasure (g.ball p r) := by
    by_contra! hzero
    have h := hbound.2
    rw [le_zero_iff.mp hzero, mul_zero] at h
    exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr).not_ge h
  exact hpos.trans_le (measure_mono fun y hy =>
    hy.trans_le (ENNReal.ofReal_le_ofReal hrR.le))

private theorem small_ball_volume_fraction
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {R δ κ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p (5 * R))))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p (5 * R), ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    {x : M} (hx : x ∈ g.ball p R) :
    (ENNReal.ofReal (modelVolume n κ (δ / 2)) /
      ENNReal.ofReal (modelVolume n κ (3 * R))) *
        g.volumeMeasure (g.ball p (2 * R)) ≤ g.volumeMeasure (g.ball x (δ / 2)) := by
  have hcontain : g.ball x (4 * R) ⊆ g.ball p (5 * R) := by
    convert ball_subset_ball_add g (by positivity) hx (by positivity : 0 ≤ 4 * R) using 1
    ring_nf
  have hcompactx : IsCompact (closure (g.ball x (4 * R))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hcontain)
  have hpx : p ∈ g.ball x R := by
    change g.edist x p < ENNReal.ofReal R
    change g.edist p x < ENNReal.ofReal R at hx
    simpa only [edist, Manifold.riemannianEDist_comm] using hx
  have hcompare : g.ball p (2 * R) ⊆ g.ball x (3 * R) := by
    convert ball_subset_ball_add g (by positivity) hpx (by positivity : 0 ≤ 2 * R) using 1
    ring_nf
  exact (mul_le_mul_of_nonneg_left (measure_mono hcompare) (by positivity)).trans
    (g.smallBall_volume_lower_bound_of_precompact_ball x hn (by positivity) hκ
      hcompactx D (fun y hy => hRic y (hcontain hy)) (by positivity)
      (by linarith) (by linarith))

private theorem separated_card_le_model_ratio
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {R δ κ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p (5 * R))))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p (5 * R), ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    (S : Finset M) (hS : (↑S : Set M) ⊆ g.ball p R)
    (hsep : (↑S : Set M).Pairwise (fun x y => ENNReal.ofReal δ ≤ g.edist x y)) :
    (S.card : ℝ) ≤ modelVolume n κ (3 * R) / modelVolume n κ (δ / 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hsmall := modelVolume_pos hn hκ (by positivity : 0 < δ / 2)
  have hlarge := modelVolume_pos hn hκ (by positivity : 0 < 3 * R)
  have hball (x : M) (r : ℝ) : Metric.eball x (ENNReal.ofReal r) = g.ball x r := by
    ext y
    change g.edist y x < ENNReal.ofReal r ↔ g.edist x y < ENNReal.ofReal r
    rw [show g.edist y x = g.edist x y from Manifold.riemannianEDist_comm]
  have h := Poincare.MeasureTheory.card_le_inv_of_relative_ball_measure
    g.volumeMeasure S (r := ENNReal.ofReal (δ / 2))
    (c := modelVolume n κ (δ / 2) / modelVolume n κ (3 * R))
    (U := g.ball p (2 * R)) (div_pos hsmall hlarge)
    (g.volumeMeasure_ball_pos p (by positivity)).ne'
    (g.volumeMeasure_ball_lt_top_of_precompact p (by positivity)
      (by linarith : 2 * R < 5 * R) hcompact).ne ?_ ?_ ?_
  · simpa only [inv_div] using h
  · intro x hx y hy hxy
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      show δ / 2 + δ / 2 = δ by ring]
    exact hsep hx hy hxy
  · intro x hx
    rw [hball]
    apply (ball_subset_ball_add g hR.le (hS hx) (by positivity)).trans
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : R + δ / 2 ≤ 2 * R))
  · intro x hx
    rw [hball, ENNReal.ofReal_div_of_pos hlarge]
    exact small_ball_volume_fraction g p hn hR hδ hδR hκ hcompact D hRic (hS hx)



theorem exists_finset_cover_of_precompact_ball
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {R δ κ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p (5 * R))))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p (5 * R), ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v) :
    ∃ S : Finset M, (↑S : Set M) ⊆ g.ball p R ∧
      S.card ≤ ⌈modelVolume n κ (3 * R) / modelVolume n κ (δ / 2)⌉₊ ∧
      (↑S : Set M).Pairwise (fun x y => ENNReal.ofReal δ ≤ g.edist x y) ∧
      g.ball p R ⊆ ⋃ x ∈ S, g.ball x δ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨S, hS, hcard, hsep, hcover⟩ :=
    Poincare.exists_finset_cover_of_separated_card_le (g.ball p R)
      (ENNReal.ofReal_pos.mpr hδ)
      ⌈modelVolume n κ (3 * R) / modelVolume n κ (δ / 2)⌉₊ (by
        intro S hS hsep
        exact_mod_cast (separated_card_le_model_ratio g p hn hR hδ hδR hκ
          hcompact D hRic S hS hsep).trans (Nat.le_ceil _))
  refine ⟨S, hS, hcard, hsep, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  refine mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  change g.edist y x < ENNReal.ofReal δ
  change g.edist x y < ENNReal.ofReal δ at hxy
  simpa only [edist, Manifold.riemannianEDist_comm] using hxy

end PoincareConjecture.RiemannianMetric

import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ValueTube








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology
namespace PoincareConjecture.RiemannianMetric



theorem closedBall_subset_common_level_tube_of_radial_margin
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (hc : PoincareConjecture.MetricComplete g)
    {ι : Type*} (f : ι → M → ℝ) {u : M → ℝ}
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (p x : M) {r s q z : ℝ} (hs : 0 < s)
    (hsr : s ≤ r / 1024) (hq : 0 < q)
    (hxrad : 9 * r / 8 < (g.edist p x).toReal ∧
      (g.edist p x).toReal < 15 * r / 8)
    (hxlevel : ∀ i, f i x = f i p)
    (hxinner : u x ∈ Ioo (z - s / 6) (z + s / 6))
    (hgradf : ∀ i y, g.edist p y ≤ ENNReal.ofReal (4 * r) →
      g.tangentNorm y (g.gradient (f i) y) ≤ 1)
    (hgradu : ∀ y, r < (g.edist p y).toReal →
      (g.edist p y).toReal < 2 * r →
      g.tangentNorm y (g.gradient u y) ≤ 1) :
    ∀ y, g.edist x y ≤ ENNReal.ofReal (min (s / 96) (q / 2)) →
      u y ∈ Ioo (z - s / 4) (z + s / 4) ∧
        ∀ i, |f i y - f i p| < q := by
  let := g.toMetricSpace
  let d := min (s / 96) (q / 2)
  have hd0 : 0 ≤ d := le_min (by positivity) (by positivity)
  have hds : d ≤ s / 96 := min_le_left _ _
  have hdq : d ≤ q / 2 := min_le_right _ _
  intro y hy
  change g.edist x y ≤ ENNReal.ofReal d at hy
  have hxy : dist x y ≤ d := by
    change (g.edist x y).toReal ≤ d
    simpa only [ENNReal.toReal_ofReal hd0] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  have hvalue := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hc hu x y
    (L := 1) (by
      intro w hw
      have hxw : dist x w ≤ (g.edist x y).toReal := by
        simpa only [Metric.mem_closedBall, dist_comm w x] using hw
      apply hgradu
      · change r < dist p w
        change 9 * r / 8 < dist p x ∧ dist p x < 15 * r / 8 at hxrad
        have htri := dist_triangle p w x
        rw [dist_comm w x] at htri
        change dist x w ≤ dist x y at hxw
        linarith [hxrad.1]
      · change dist p w < 2 * r
        change 9 * r / 8 < dist p x ∧ dist p x < 15 * r / 8 at hxrad
        have htri := dist_triangle p x w
        change dist x w ≤ dist x y at hxw
        linarith [hxrad.2])
  simp only [NNReal.coe_one, one_mul] at hvalue
  have hdiff : |u y - u x| ≤ s / 96 := hvalue.trans (hxy.trans hds)
  have hfgap := g.value_gap_le_of_mem_closedBall_common_level hc f hf p x hd0
    hxlevel (R := 4 * r) (by linarith [hxrad.2]) hgradf y hy
  refine ⟨?_, fun i => (hfgap i).trans_lt (by linarith)⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
  constructor <;> linarith [hxinner.1, hxinner.2]



theorem closedBall_subset_common_level_tube_of_normalized_slab
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (hc : PoincareConjecture.MetricComplete g)
    {ι : Type*} (f : ι → M → ℝ) {u : M → ℝ}
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (p : M) {r τ ε q t : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : ε ≤ r / 65536) (hq : 0 < q)
    (ht : t ∈ Icc (7 * r / 12) (9 * r / 10))
    (hband : ∀ y, u y ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) →
      r < (g.edist p y).toReal ∧ (g.edist p y).toReal < 2 * r)
    (hcore : ∀ y, r < (g.edist p y).toReal → (g.edist p y).toReal < 2 * r →
      |u y - τ * (g.edist p y).toReal| ≤ τ * ε ∧
      g.tangentNorm y (g.gradient u y) ≤ 1)
    (hgradf : ∀ i y, g.edist p y ≤ ENNReal.ofReal (4 * r) →
      g.tangentNorm y (g.gradient (f i) y) ≤ 1) :
    let s := τ * r / 1024
    ∀ x : M, (∀ i, f i x = f i p) →
      u x ∈ Ioo (2 * τ * t - s / 6) (2 * τ * t + s / 6) →
      ∀ y, g.edist x y ≤ ENNReal.ofReal (min (s / 96) (q / 2)) →
        u y ∈ Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4) ∧
          ∀ i, |f i y - f i p| < q := by
  dsimp only
  let s := τ * r / 1024
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s ≤ r / 1024 := by
    have h := mul_le_mul_of_nonneg_right hτ1 hr.le
    dsimp [s]
    linarith
  intro x hxlevel hxinner
  have hτr := mul_pos hτ hr
  have hlo := mul_le_mul_of_nonneg_left ht.1 hτ.le
  have hhi := mul_le_mul_of_nonneg_left ht.2 hτ.le
  have hxI : u x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) := by
    change 2 * τ * t - (τ * r / 1024) / 6 < u x ∧
      u x < 2 * τ * t + (τ * r / 1024) / 6 at hxinner
    constructor <;> nlinarith only [hxinner.1, hxinner.2, hlo, hhi, hτr]
  have hxcore := hband x hxI
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp (hcore x hxcore.1 hxcore.2).1
  have he := mul_le_mul_of_nonneg_left hε hτ.le
  have hxrad : 9 * r / 8 < (g.edist p x).toReal ∧
      (g.edist p x).toReal < 15 * r / 8 := by
    change 2 * τ * t - (τ * r / 1024) / 6 < u x ∧
      u x < 2 * τ * t + (τ * r / 1024) / 6 at hxinner
    constructor
    · apply (mul_lt_mul_iff_right₀ hτ).mp
      nlinarith only [hxinner.1, hlo, hdhi, he, hτr]
    · apply (mul_lt_mul_iff_right₀ hτ).mp
      nlinarith only [hxinner.2, hhi, hdlo, he, hτr]
  exact g.closedBall_subset_common_level_tube_of_radial_margin
    hc f hf hu p x hs hsr hq hxrad hxlevel hxinner hgradf
    (fun y hy hy' => (hcore y hy hy').2)

end PoincareConjecture.RiemannianMetric

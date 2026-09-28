import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.TightScaleSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.OppositeLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Proper

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

private theorem distance_pair_slab_parameters {r τ ε : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : ε ≤ r / 128) :
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    let t := 3 * τ * r / 2
    let s := τ * r / 128
    0 < s ∧ s ≤ 1 ∧ (5 / r) * s ≤ 1 ∧
      Icc (t - 2 * s) (t - s) ⊆ I ∧
      ∀ a d : ℝ, a ∈ Icc (t - 2 * s) (t - s) →
        |a - τ * d| ≤ τ * ε → 5 * r / 4 < d ∧ d < 7 * r / 4 := by
  have hτr : 0 < τ * r := mul_pos hτ hr
  have hτrle : τ * r ≤ r := by nlinarith
  have herror : τ * ε ≤ τ * (r / 128) := mul_le_mul_of_nonneg_left hε hτ.le
  have hHs : (5 / r) * (τ * r / 128) = 5 * τ / 128 := by
    field_simp
  dsimp only
  refine ⟨by positivity, by nlinarith, ?_, ?_, ?_⟩
  · rw [hHs]
    linarith
  · intro a ha
    constructor <;> nlinarith only [ha.1, ha.2, hτr]
  · intro a d ha happrox
    obtain ⟨hlo, hhi⟩ := abs_le.mp happrox
    constructor
    · apply (mul_lt_mul_iff_right₀ hτ).mp
      nlinarith only [ha.1, hhi, herror, hτr]
    · apply (mul_lt_mul_iff_right₀ hτ).mp
      nlinarith only [ha.2, hlo, herror, hτr]

theorem exists_compact_regular_slab_with_near_opposite_pair
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - δ ^ 2 / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    letI := g.toMetricSpace
    let τ := 1 / (1 + δ ^ 2 / 8)
    let ε := δ ^ 4 * r / 1048576
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    let t := 3 * τ * r / 2
    let s := τ * r / 128
    ∃ f rho : M → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      IsProperMap (I.restrictPreimage f) ∧
      (∀ x : M, f x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |f x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
        1 - δ ^ 2 ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) x,
          D.hessian f x v v ≤ (5 / r) * g.inner x v v) ∧
      IsCompact (f ⁻¹' Icc (t - 2 * s) (t - s)) ∧
      ∀ x ∈ f ⁻¹' Icc (t - 2 * s) (t - s),
        |rho x - Metric.infDist x (f ⁻¹' {t})| ≤ δ ^ 2 * s ∧
        g.tangentNorm x (D.gradient rho x) ≤ 1 + δ ^ 2 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian rho x v v ≤ (3 / s) * g.inner x v v) ∧
        g.tangentNorm x (D.gradient f x + D.gradient rho x) ≤ 64 * δ := by
  let := g.toMetricSpace
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let τ := 1 / (1 + δ ^ 2 / 8)
  let ε := δ ^ 4 * r / 1048576
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  let t := 3 * τ * r / 2
  let s := τ * r / 128
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδ2quarter : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hδ4 : δ ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ hδ.le (show δ ≤ 1 by linarith) 4
    norm_num at h
    exact h
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp only [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg δ]
  have hε : ε ≤ r / 128 := by
    have h := mul_le_mul_of_nonneg_right hδ4 hr.le
    dsimp only [ε]
    linarith
  obtain ⟨hs, hs1, hHs, hband, hradial⟩ :=
    distance_pair_slab_parameters hr hr1 hτ hτ1 hε
  change 0 < s at hs
  change s ≤ 1 at hs1
  change (5 / r) * s ≤ 1 at hHs
  change Icc (t - 2 * s) (t - s) ⊆ I at hband
  obtain ⟨f, hf, hproper, hreg, hrange, hcore⟩ :=
    g.exists_proper_regular_slab_with_near_unit_gradient D hc hsec p
      hr hr1 hδ2 hδ2quarter hascent
  have hεeq : (δ ^ 2) ^ 2 * r / 1048576 = ε := by dsimp only [ε]; ring
  have hcore' : ∀ x : M,
      r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |f x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
        1 - δ ^ 2 ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) x,
          D.hessian f x v v ≤ (5 / r) * g.inner x v v := by
    simpa only [hεeq] using hcore
  let T := f ⁻¹' Icc (t - 2 * s) (t - s)
  have hT : IsCompact T := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hband
  have hgap : ∀ x ∈ T, s ≤ t - f x ∧ t - f x ≤ 2 * s := by
    intro x hx
    change f x ∈ Icc (t - 2 * s) (t - s) at hx
    constructor <;> linarith [hx.1, hx.2]
  have hbuffer : ∀ x ∈ T, ∀ y ∈ Metric.closedBall x (4 * s),
      1 - δ ^ 2 ≤ g.tangentNorm y (D.gradient f y) ∧
      g.tangentNorm y (D.gradient f y) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) y,
        D.hessian f y v v ≤ (5 / r) * g.inner y v v := by
    intro x hx y hy
    have hxcore := hrange x (hband hx)
    obtain ⟨hxlo, hxhi⟩ := hradial (f x) (g.edist p x).toReal hx
      (hcore' x hxcore.1 hxcore.2).1
    change 5 * r / 4 < dist p x at hxlo
    change dist p x < 7 * r / 4 at hxhi
    have hxy : dist x y ≤ 4 * s := by
      simpa only [Metric.mem_closedBall, dist_comm] using hy
    have h4s : 4 * s ≤ r / 32 := by
      have h := mul_le_mul_of_nonneg_right hτ1 hr.le
      dsimp only [s]
      nlinarith only [h]
    have hylo : r < (g.edist p y).toReal := by
      change r < dist p y
      have htri := dist_triangle p y x
      rw [dist_comm y x] at htri
      linarith
    have hyhi : (g.edist p y).toReal < 2 * r := by
      change dist p y < 2 * r
      have htri := dist_triangle p x y
      linarith
    exact (hcore' y hylo hyhi).2
  obtain ⟨rho, hrho, hpair⟩ :=
    g.exists_near_opposite_smoothing_of_upper_level D hc hsec hf hT
      hs hs1 hδ hδ16 (by positivity) hHs hgap hbuffer
  exact ⟨f, rho, hf, hrho, hproper, hreg, hrange, hcore', hT, hpair⟩

end PoincareConjecture.RiemannianMetric
